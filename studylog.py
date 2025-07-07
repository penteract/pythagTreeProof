f=open("log3.txt")
ftxt="".join(f)
ls =ftxt.split("]]")
ps = ls[1].split("],")
pss = [[k.strip("\n[ ") for k in x.split(",") ] for x in ps]
print(len(pss))
ll = [x for x in pss if any(['Piece.treePiece 0 3' in k for k in x])]
print(len(ll))
