#!/usr/bin/env python3
"""Read archived compiler outputs; collect bounded parallel-region evidence.

No compiler invocation or source/proof changes. This deliberately does not infer
retention from a pragma count. It records each nonempty parallel iteration's
ordered address trace and reports concrete cross-iteration access conflicts.
"""
import argparse
import collections
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

BASE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("retention_trace", BASE / "retention_trace.py")
rt = importlib.util.module_from_spec(spec)
spec.loader.exec_module(rt)

HELPERS = r'''
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <stdint.h>
#include <limits.h>
static long long tile[32]; static int tile_dimensions;
static int depth=0, kinds[128], regions[128], iterations[128], next_region=0;
static unsigned long long records=0, events=0;
static void event(long long tag,long long value) {
  if (++events>2000000) {puts("TRUNCATED");exit(77);}
  if(tag==101 || tag==102) {
    kinds[depth]=tag;regions[depth]=tag==102?++next_region:0;
    iterations[depth]=-1;depth++;
  } else if(tag==103) iterations[depth-1]++;
  else if(tag==105) depth--;
}
static void record(const char *tag,int n,...) {
  if(++records>250000){puts("TRUNCATED");exit(77);}
  for(int i=0;i<depth;i++)if(kinds[i]==102)printf("%d:%d,",regions[i],iterations[i]);
  printf("|%s",tag); va_list a;va_start(a,n);
  for(int i=0;i<n;i++)printf("|%lld",va_arg(a,long long));
  va_end(a);puts("");
}
static long long polcert_z_div(long long x,long long y) {if(!y)return 0;long long q=x/y,r=x%y;return q-((r!=0)&&((r<0)!=(y<0)));}
static long long polcert_z_mod(long long x,long long y) {return y?x-y*polcert_z_div(x,y):x;}
#define floord(x,y) polcert_z_div((x),(y))
#define ceild(x,y) (-polcert_z_div(-(x),(y)))
#define min(x,y) ((x)<(y)?(x):(y))
#define max(x,y) ((x)>(y)?(x):(y))
'''

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def build(body, params, target):
    macros=[];lines=[]
    for line in body.splitlines():
        if line.lstrip().startswith('#include'):continue
        (macros if line.lstrip().startswith('#define') else lines).append(line)
    declarations='\n'.join(f'long long {name}=atoll(argv[{i+1}]);' for i,name in enumerate(params))
    src=HELPERS+'\n'+'\n'.join(macros)+'\nint main(int argc,char**argv){\n'+declarations+'\n'+'\n'.join(lines)+'\nputs("COMPLETE");}\n'
    target.with_suffix('.c').write_text(src)
    p=subprocess.run(['gcc','-std=gnu11','-O0','-w',str(target.with_suffix('.c')),'-o',str(target)],capture_output=True,text=True,timeout=15)
    if p.returncode:raise ValueError(p.stderr[:2000])

def run(exe, values):
    p=subprocess.run([str(exe),*map(str,values)],capture_output=True,text=True,timeout=5)
    regions=collections.defaultdict(lambda:collections.defaultdict(list))
    access=hashlib.sha256();n=0;first_conflict=None;seen={};first_events=[]
    for line in p.stdout.splitlines():
        if '|' not in line:continue
        fields=line.split('|');context=[tuple(map(int,v.split(':'))) for v in fields[0].rstrip(',').split(',') if v]
        tag=fields[1];indices=list(map(int,fields[2:]));record=fields[1:]
        encoded=json.dumps(record,separators=(',',':')).encode();access.update(encoded+b'\n');n+=1
        for region,iteration in context:regions[region][iteration].append(encoded)
        if len(first_events)<3:first_events.append({'context':context,'record':record})
        cursor=0
        for part in tag.split(';'):
            mode,location=part.split(':',1);nd=location.count('[]');addr=(location.replace('[]',''),tuple(indices[cursor:cursor+nd]));cursor+=nd
            if mode not in ('W','R'):continue
            for region,iteration in context:
                key=(region,addr);previous=seen.get(key)
                if previous and previous['iteration']!=iteration and (mode=='W' or previous['mode']=='W') and first_conflict is None:
                    first_conflict={'region':region,'address':[addr[0],list(addr[1])], 'first':previous,'second':{'iteration':iteration,'mode':mode,'record':record,'ordinal':n}}
                if previous is None or mode=='W':seen[key]={'iteration':iteration,'mode':mode,'record':record,'ordinal':n}
    groups=[]
    for region,threads in regions.items():
        # Empty iterations contribute no possible cross-thread instruction pair.
        if len(threads)<2:continue
        groups.append([{'statements':len(items),'sha256':hashlib.sha256(b'\n'.join(items)).hexdigest()} for _,items in sorted(threads.items())])
    return {'complete':p.returncode==0 and p.stdout.rstrip().endswith('COMPLETE'),'returncode':p.returncode,'statements':n,'access_sha256':access.hexdigest(),'nontrivial_nonempty_regions':len(groups),'iteration_groups':groups,'first_conflict':first_conflict,'first_events':first_events}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('retention',type=Path);ap.add_argument('--source-root',type=Path,required=True);ap.add_argument('--only',nargs='+');args=ap.parse_args()
    out=args.retention/'parallel-review-raw';out.mkdir(exist_ok=True)
    trans=rt.load_transpiler(args.source_root)
    rows=json.loads((args.retention/'retention-rows.json').read_text());results=[]
    for row in rows:
        if args.only:
            if row['id'] not in args.only:continue
        elif row['configuration']!='parallel' or row['effects']['parallelization']['retention'] not in ('unresolved','sampled-retained'):continue
        case=args.retention/'cases'/row['id'];target=out/row['id'];target.mkdir(exist_ok=True)
        old=json.loads((case/'trace-comparison.json').read_text());meta=json.loads((case/'result.json').read_text());stdout=(case/'polcert.stdout.txt').read_text()
        captures=sorted((case/'pluto').glob('*/output.pluto.c'))
        if old.get('producer_file'):producer=args.retention/Path(old['producer_file']).relative_to('/tmp/polcert-retention-2026-09-04')
        else:producer=next((f for f in captures if '#pragma omp parallel'in f.read_text()),None)
        entry={'id':row['id'],'old':row['effects']['parallelization'],'producer_file':str(producer),'observations':[]}
        if producer is None:results.append(entry);continue
        final=stdout.split('== Optimized Loop ==',1)[-1].strip() if '== Optimized Loop =='in stdout else None
        source=args.source_root/meta['source_relative'];params=rt.params_from_loop(source.read_text());entry['parameters']=params;entry['producer_sha256']=sha(producer);entry['final_sha256']=sha(case/'polcert.stdout.txt')
        try:
            build(rt.instrument(producer.read_text(),parameters=params),params,target/'pluto')
            if final:build(rt.instrument(trans.transpile_loop_text(final),parameters=params),params,target/'polcert')
        except Exception as ex:entry['error']=str(ex);results.append(entry);continue
        samples=[s['parameters'] for s in old.get('observations',[]) if s['pluto']['status']=='ok' and s['pluto']['parallel_loops']>0]
        if row['effects']['parallelization']['retention']=='unresolved':samples=samples[:1]
        samples=[dict(items) for items in dict.fromkeys(tuple(sorted(s.items())) for s in samples)]
        if not samples:
            samples=[{name:37 for name in params}]
        if row['kernel']=='diamond-example-inner-batch':samples=[{'B':37,'T':7,'N':11},{'B':65,'T':9,'N':13}]
        if row['kernel']=='jacobi-batch':samples=[{'B':37,'T':3,'N':5},{'B':65,'T':5,'N':7}]
        if row['kernel'] in ['fusion7','multi-loop-param']:samples=[dict(zip(params,[259]+[3]*(len(params)-1))),{name:37 for name in params}]
        if row['kernel'] in ['pca','corcol']:samples=[{name:(37 if name.lower()=='m' else 3) for name in params}]
        if row['kernel']=='adi':samples=[{'T':2,'N':37}]
        if row['kernel'] in ['fusion3','fusion4','tce']:entry['skip_reason']='Full domain too large; static review required';results.append(entry);continue
        for sample in samples:
            obs={'parameters':sample}
            for name in ['pluto','polcert']:
                if name=='polcert' and not final:continue
                try:obs[name]=run(target/name,[sample[v] for v in params])
                except Exception as ex:obs[name]={'error':str(ex)}
            if 'polcert'in obs and 'access_sha256'in obs['polcert']:
                a,b=obs['pluto'],obs['polcert'];obs['complete_access_match']=a['complete'] and b['complete'] and a['access_sha256']==b['access_sha256'];obs['complete_parallel_group_match']=obs['complete_access_match'] and a['iteration_groups']==b['iteration_groups']
            entry['observations'].append(obs)
        (target/'evidence.json').write_text(json.dumps(entry,indent=2)+'\n');results.append(entry)
        print(row['id'],[(x['parameters'],x.get('complete_parallel_group_match'),x.get('pluto',{}).get('nontrivial_nonempty_regions'),bool(x.get('pluto',{}).get('first_conflict'))) for x in entry['observations']],flush=True)
    filename='bounded-extra-evidence.json' if args.only else 'bounded-evidence.json'
    (out/filename).write_text(json.dumps({'script_sha256':sha(Path(__file__)),'limit_statements':250000,'results':results},indent=2)+'\n')

if __name__=='__main__':main()
