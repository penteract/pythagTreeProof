f=open("log3.txt")
ftxt="".join(f)
ls =ftxt.split("]]")
ps = ls[1].split("],")
pss = [[k.strip("\n[ ") for k in x.split(",") ] for x in ps]
print(len(pss))
ll = [x for x in pss if any(['Piece.treePiece 0 3' in k for k in x])]
print(len(ll))
f=open("log5.txt")
ftxt="".join(f)

ftxt=ftxt[ftxt.find("info: /mnt/old/home/toby/fun/pythagTree/formalproof/Proof/Concrete.lean:53:0"):]
ps = [x[1:] for x in ftxt.split(")")[:-1]]
print(len(ps))
def procList(l):
    return [y for y in [x.strip("[] \n)(") for x in l.split(",")] if y]

ps = [(procList(a),list(map(procList,b.split("[")))) for x in ps for a,b in [x.split("[[")]]
# ps = [[k.strip("[] \n)(") for k in x.split(",")] for x in ps]

ps[0] = ([],ps[0][1])
assert all(len(b)==4 for a,b in ps)
# ps = ps[1:len(ps)-1] # first and last are not useful equations
ks = {str(a[0]):n for n,a in enumerate(ps)}
assert all( str(x) in ks for a,b in ps for x in b)
# d = {a:b for a,b in ps}
import sympy
from sympy.solvers.solveset import linsolve
from sympy.solvers.solveset import linear_eq_to_matrix
def var(n):
    return sympy.var("x_"+str(ks[str(n)]))
es = ([var([]), var(['Piece.fullPiece']) - 1 ] +
       [var(a)*4 - sum(var(x) for x in b) for a,b in ps
          if str(a) not in ["[]","['Piece.fullPiece']"]])
vs = [var(a) for a,b in ps]
A,b=linear_eq_to_matrix(es,vs)
At=A.transpose()
from sympy import Matrix


# r = linsolve(es,vs)
baseTree=[
  "Piece.treePiece 0 0 0",
  "Piece.treePiece 0 1 0",
  "Piece.treePiece 0 2 0",
  "Piece.treePiece 0 3 0",
  "Piece.treePiece 1 0 0",
  "Piece.treePiece 1 1 0",
  "Piece.treePiece 1 2 0",
  "Piece.treePiece 1 3 0",
  "Piece.treePiece 2 0 0",
  "Piece.treePiece 2 1 0",
  "Piece.treePiece 2 2 0",
  "Piece.treePiece 2 3 0",
  "Piece.treePiece 3 0 0",
  "Piece.treePiece 3 1 0",
  "Piece.treePiece 3 2 0",
  "Piece.treePiece 3 3 0",
  "Piece.treePiece 4 0 0",
  "Piece.treePiece 4 1 0",
  "Piece.treePiece 4 2 0",
  "Piece.treePiece 4 3 0",
  "Piece.treePiece 5 0 0",
  "Piece.treePiece 5 1 0",
  "Piece.treePiece 5 2 0",
  "Piece.treePiece 5 3 0",
  "Piece.treePiece 6 0 0",
  "Piece.treePiece 6 1 0",
  "Piece.treePiece 6 2 0",
  "Piece.treePiece 6 3 0"]
# res = list(r)[0]
# print(sum(res[ks[str([p])]] for p in baseTree))


base = [ks[str([p])] for p in baseTree]
v = [0]*len(b)
for p in baseTree: v[ks[str([p])]]=1 # add one because the equations got shifted around
v = Matrix([[x] for x in v])
system = (At,v)
import time
t = time.perf_counter()
r = linsolve(system)
print("time to solve",time.perf_counter()-t)
res = list(r)[0]



N = 40
class C:
    def __init__(self,s):
        self.s=s
    def __repr__(self):
        return self.s
# there's something at least quadratic in lean's list parser
# we want to make lists of type 'List (List Piece × List (List Piece) × ℚ)'
def genFile(N,fname):
    with open(fname,mode="w") as f:
        print("import Mathlib\nimport Proof.TileArea\n",file=f)
        k = (len(ps)+N-1)//N
        for part in range(N):
            print(f"def part{part}: List (List Piece × List (List Piece) × ℚ) :=[",file=f)
            top = min((part+1)*k,len(ps))
            for j in range(k*part,top):
                p=ps[j]
                print(" ",(list(map(C,p[0])),[[C(x) for x in y] for y in p[1]],res[j]) ,","*(j!=top-1),file=f)
            print(f"]",file=f)
        print(f"def allparts: List (List Piece × List (List Piece) × ℚ) :=","++".join(f"part{part}" for part in range(N)),file=f)


def genFile2(N,fname):
    with open(fname,mode="w") as f:
        print("import Mathlib\nimport Proof.TileArea\n",file=f)
        print("-- vol' e.1 =sum(vol' e.2)/4; e.3 is the coefficient of this eqn for linear_combination",file=f)
        k = ((len(ps)-2)+N-1)//N #ignore the first and last elements of ps
        for part in range(N):
            print(f"def part{part}: List (List Piece × List (List Piece) × ℚ) :=[",file=f)
            top = min((part+1)*k,len(ps)-2) #ignore the first and last elements of ps
            for j in range(k*part,top):
                p=ps[j+1] # handle the shifted eqns
                print(" ",(list(map(C,p[0])),[[C(x) for x in y] for y in p[1]],res[j+2]) ,","*(j!=top-1),file=f)
            print(f"]",file=f)
        print(f"def allparts: List (List Piece × List (List Piece) × ℚ) :=","++".join(f"part{part}" for part in range(N)),file=f)
        print(f"def qFull:  ℚ :=",res[1],file=f)
        print(f"def qEmpty:  ℚ :=",res[1],file=f)
        
