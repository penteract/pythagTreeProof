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

ks = {str(a[0]):n for n,a in enumerate(ps)}
assert all( str(x) in ks for a,b in ps for x in b)
# d = {a:b for a,b in ps}
import sympy
from sympy.solvers.solveset import linsolve
def var(n):
    return sympy.var("x_"+str(ks[str(n)]))
es = [var([]), var(['Piece.fullPiece']) - 1 ]+[var(a)*4 - sum(var(x) for x in b) for a,b in ps]
vs = [var(a) for a,b in ps]
r = linsolve(es,vs)
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
res = list(r)[0]
print(sum(res[ks[str([p])]] for p in baseTree))
