"""Check of Corollary hinted's core identity over Q (exact rational arithmetic):
X = block upper-unitriangular 0/1 matrix with U,R1,N,R2,V on the superdiagonal;
rank_Q [[X, e_b],[e_a^T, 0]] = m + [Boolean (U R1 N R2 V)_{ab} = 1]."""
import random
from fractions import Fraction
def rank_q(M):
    M=[[Fraction(x) for x in row] for row in M]; r=0; rows=len(M); cols=len(M[0])
    for c in range(cols):
        piv=next((i for i in range(r,rows) if M[i][c]!=0),None)
        if piv is None: continue
        M[r],M[piv]=M[piv],M[r]
        for i in range(rows):
            if i!=r and M[i][c]!=0:
                f=M[i][c]/M[r][c]; M[i]=[a-f*b for a,b in zip(M[i],M[r])]
        r+=1
    return r
def bool_prod(*Ms):
    P=Ms[0]
    for Q in Ms[1:]:
        P=[[int(any(P[i][k] and Q[k][j] for k in range(len(Q)))) for j in range(len(Q[0]))] for i in range(len(P))]
    return P
rng=random.Random(5); ok=tot=0
for _ in range(60):
    n=rng.randint(1,3); t1=rng.randint(1,3); t2=rng.randint(1,3)
    R=lambda a,b,p: [[int(rng.random()<p) for _ in range(b)] for _ in range(a)]
    U,R1,N,R2,V=R(n,t1,.5),R(t1,n,.4),R(n,n,.5),R(n,t2,.4),R(t2,n,.5)
    blocks=[n,t1,n,n,t2,n]; off=[0]
    for b in blocks: off.append(off[-1]+b)
    m=off[-1]; X=[[int(i==j) for j in range(m)] for i in range(m)]
    for bi,A in enumerate([U,R1,N,R2,V]):
        for i,row in enumerate(A):
            for j,v in enumerate(row):
                X[off[bi]+i][off[bi+1]+j]=v
    P=bool_prod(U,R1,N,R2,V)
    a=rng.randrange(n); b=rng.randrange(n)
    ap=off[0]+a; bp=off[5]+b
    Bd=[row[:]+[int(i==bp)] for i,row in enumerate(X)]+[[int(j==ap) for j in range(m)]+[0]]
    tot+=1; ok+= rank_q(Bd)==m+P[a][b]
print(f"rank_Q(bordered X) = m + Boolean(U R1 N R2 V)_ab: {ok}/{tot}")
print('ALL VALIDATED:', ok==tot)
