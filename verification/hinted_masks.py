"""Check of the masking step in the proof of Corollary cor:hinted (Section 5.4).

Not part of any proof.  For random Boolean matrices M1..M5 we mask M1, M3, M5
entrywise with uniformly random 0/1 matrices and evaluate the product over F_p.
We check: (a) if the Boolean entry (a,b) is 0, the masked entry is 0 in F_p for
every mask; (b) if it is 1, the masked entry is nonzero for at least 1/8 of
all masks (computed exactly by enumerating the relevant mask bits on small
instances); (c) the bordered-rank identity rank [[X, e_b'], [e_a'^T, 0]] =
m + [entry != 0] for the block-unitriangular matrix X over F_p.
Standard library only.
"""
import itertools, random

def matmul(A, B, p):
    n, k, m = len(A), len(B), len(B[0])
    return [[sum(A[i][t] * B[t][j] for t in range(k)) % p for j in range(m)] for i in range(n)]

def rank_mod(M, p):
    M = [row[:] for row in M]; r = 0; rows, cols = len(M), len(M[0])
    for c in range(cols):
        piv = next((i for i in range(r, rows) if M[i][c] % p), None)
        if piv is None: continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], p - 2, p)
        M[r] = [x * inv % p for x in M[r]]
        for i in range(rows):
            if i != r and M[i][c] % p:
                f = M[i][c]; M[i] = [(x - f * y) % p for x, y in zip(M[i], M[r])]
        r += 1
    return r

def block_X(mats, p):
    sizes = [len(mats[0])] + [len(Mt[0]) for Mt in mats]
    offs = [0]
    for s in sizes: offs.append(offs[-1] + s)
    m = offs[-1]
    X = [[1 if i == j else 0 for j in range(m)] for i in range(m)]
    for t, Mt in enumerate(mats):
        for i, row in enumerate(Mt):
            for j, x in enumerate(row):
                X[offs[t] + i][offs[t + 1] + j] = x % p
    return X, offs

def main():
    random.seed(7)
    ok = True; cases = 0
    for p in (2, 3, 5):
        for _ in range(40):
            s = random.randint(1, 3)
            dims = [random.randint(1, s + 1) for _ in range(6)]
            M = [[[1 if random.random() < 0.5 else 0 for _ in range(dims[t + 1])] for _ in range(dims[t])] for t in range(5)]
            Bool = M[0]
            for t in range(1, 5):
                Bool = [[1 if any(Bool[i][k] and M[t][k][j] for k in range(len(M[t]))) else 0 for j in range(len(M[t][0]))] for i in range(len(Bool))]
            a, b = random.randrange(dims[0]), random.randrange(dims[5])
            # mask bits that can matter: row a of M1, all of M3, column b of M5
            pos1 = [(a, i) for i in range(dims[1])]
            pos3 = [(i, j) for i in range(dims[2]) for j in range(dims[3])]
            pos5 = [(i, b) for i in range(dims[4])]
            bits = len(pos1) + len(pos3) + len(pos5)
            if bits > 14: continue
            nonzero = 0; total = 0
            for mask in itertools.product((0, 1), repeat=bits):
                X1 = [row[:] for row in M[0]]; X3 = [row[:] for row in M[2]]; X5 = [row[:] for row in M[4]]
                it = iter(mask)
                for (i, j) in pos1: X1[i][j] *= next(it)
                for (i, j) in pos3: X3[i][j] *= next(it)
                for (i, j) in pos5: X5[i][j] *= next(it)
                P = matmul(matmul(matmul(matmul(X1, M[1], p), X3, p), M[3], p), X5, p)
                val = P[a][b] % p
                total += 1; nonzero += (val != 0)
                if total <= 3:  # bordered-rank identity on a few masks
                    X, offs = block_X([X1, M[1], X3, M[3], X5], p)
                    m = len(X)
                    B = [row[:] + [0] for row in X] + [[0] * (m + 1)]
                    B[offs[0] + a][m] = 0
                    B[m][offs[0] + a] = 1
                    B[offs[5] + b][m] = 0
                    B[offs[5] + b][m] = 0
                    # border: column e_{b'} (row index of last block col b) and row e_{a'}^T
                    Bm = [row[:] + [1 if r == offs[5] + b else 0] for r, row in enumerate(X)] + [[1 if c == offs[0] + a else 0 for c in range(m)] + [0]]
                    ok &= rank_mod(Bm, p) == m + (1 if val else 0)
            if Bool[a][b] == 0: ok &= (nonzero == 0)
            else: ok &= (nonzero * 8 >= total)
            cases += 1
    print('instances:', cases, 'masking and bordered-rank checks correct:', ok)
    print('ALL VALIDATED:', ok)

if __name__ == '__main__':
    main()
