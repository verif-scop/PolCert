#!/usr/bin/env python3
"""Build bounded parallel-region trace observations.

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
