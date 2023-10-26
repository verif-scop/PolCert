%token <Z.t> Z
%token SX SLASH EOL EOF MATRIX FRONTIERS NO_FRONTIERS EXPLORATION_POINT TODO REGION PROBLEM NO_POINT POINTS
%start problem
%start one_sx
%start points
%type <PLPBuild.DescPoints.t> points
%type <PLPBuild.DescSx.t> one_sx
%type <PLPBuild.DescSlave.t> problem
%type <Z.t list> basis
%type <((Q.t list) * ((Q.t * Q.t) list)) list> boundaries
%type <Q.t list> cons
%type <(Q.t list) list> cs
%type <Z.t * (Q.t list) * ((Q.t * Q.t) list)> explorationPoint
%type <(Z.t * (Q.t list) * ((Q.t * Q.t) list)) list> explorationPoints
%type <((Q.t list) * ((Q.t * Q.t) list)) list> frontiers
%type <Q.t> nb
%type <Z.t list> parameters
%type <(Q.t * Q.t) list> point
%type <PLPBuild.DescReg.t> reg
%type <PLPBuild.DescReg.t> sx
%type <Z.t list> variables
%type <int> work_todo
%%
problem : PROBLEM EOL reg explorationPoints work_todo EOF {PLPBuild.DescSlave.mk $3 $4 $5}
;
reg : REGION Z EOL point sx frontiers {PLPBuild.DescReg.mk (Z.to_int $2) $4 $5 $6}
;
one_sx: sx EOF {$1}
;
sx : SX Z Z EOL basis variables parameters cs MATRIX EOL cs {PLPBuild.DescSx.mk $2 $3 $5 $6 $7 $8 $11}
;
points : POINTS EOL explorationPoints EOF {$3}
;
point : 
  nb nb EOL {[($1, $2)]}
| nb nb point {($1,$2) :: $3}
;
basis : 
  EOL {[]}
| Z basis {$1 :: $2}
;
variables : basis {$1}
;
parameters : basis {$1}
;
boundaries: 
  cons point {[($1,$2)]}
| cons point boundaries {($1,$2) :: $3}
;
frontiers : 
	NO_FRONTIERS EOL {[]}
| 	FRONTIERS EOL boundaries {$3}
;
cs:
  cons {[$1]}
| cons cs {$1 :: $2}
;
cons:
  nb EOL {[$1]}
| nb cons {$1 :: $2}
;
nb:
  Z {Q.make $1 Z.one}
| Z SLASH Z {Q.make $1 $3}
;
explorationPoint: EXPLORATION_POINT Z EOL cons point {(Z.to_int $2,$4,$5)}
;
explorationPoints: 
| NO_POINT EOL {[]}
| explorationPoint {[$1]}
| explorationPoint explorationPoints {$1 :: $2}
;
work_todo : TODO Z EOL {Z.to_int $2}
;
