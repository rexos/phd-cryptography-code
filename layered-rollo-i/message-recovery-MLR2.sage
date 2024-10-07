reset()
from sage.doctest.util import Timer

# parameters for modified Layered-ROLLO-I
# 128 bits
q, m, degPI, n1, n2, nn = 2,67,4,37,61,1
# 192 bits
#q, m, degPI, n1, n2, nn = 2,79,4,43,71,2
# 256 bits security
#q, m, degPI, n1, n2, nn = 2,97,4,53,103,4

# Choices of P1 according to modified Layered-ROLLO-I implementation
# WE DO NOT CARE WHAT P1 IS. MIGHT AS WELL BE RANDOM.
# 128 bits
P1=x^37 + x^22 + x^14 + x^2 + 1
# 192 bits
#P1=x^43 + x^27 + x^22 + x^5 + 1
# 256 bits
#P1 = x^53 + x^50 + x^41 +x^20 + 1


lenE = n2 - n1- degPI - nn - 2
degE = lenE-1
print(degE)

Fqm = GF(q^m)
P.<x> = Fqm[]
F2x.<x> = GF(2)[]

def pis(G,y):
  M = copy(G)
  k,n = M.dimensions()
  p = list(Permutations(n).random_element())
  p = list(range(lenE+1,n2))
  shuffle(p)
  indexes = p[:k]
  indexes.sort()
  colsG = [M.columns()[i-1] for i in indexes]
  colsy = [y.columns()[i-1] for i in indexes]
  pisG = matrix(Fqm, colsG)
  pisy = matrix(Fqm, colsy)
  return pisG.transpose(), pisy.transpose()
  
  
def Prange(M, y, t):
  k,n = M.dimensions()
  while True:
    M1,y1 = pis(M,y)
    while not M1.is_invertible():
      M1,y1 = pis(M,y)
    U = M1.inverse()
    msg = y1*U
    x = msg*M
    wt = len([i for i in range(n) if x[0][i] != y[0][i]])
    if wt <= t:
      e = y - x
      return msg, e






def getmultmatrix(R,P2,nrows):
  M = []
  for i in range(n2):
    el = list((R*x^i).mod(P2))
    M.append(el + [0 for j in range(n2-len(el))])
  M = matrix(Fqm,M)
  return M[:nrows,:]


V = VectorSpace(Fqm,n1)
u,v = V.random_element(), V.random_element()
Pu, Pv = P(list(u)), P(list(v))

P2 = F2x.irreducible_element(n2)
P1 = P(P1)
P2 = P(P2)
PI = P.random_element(degPI)
PO = P(list(VectorSpace(Fqm,n2+1).random_element()))
PN = P.random_element(1)
xy = (Pu.inverse_mod(P1)*Pv).mod(P1)
z = (PI*xy).mod(P1)
lz = list(z) + [0 for j in range(0,n2-len(list(z)))]
#PP, PH = (PO*PI).mod(P2), (PO*z).mod(P2)

time = 0
timer = Timer()
for i in range(50):
  E1 = P.random_element(degE)
  E2 = P.random_element(degE)
  #### PUBLIC DATA
  PP, PH = (PO*(PI + PN*P1)).mod(P2), (PO*z).mod(P2)
  PC = (PP*E1 + PH*E2).mod(P2)

  timer.start()
  #### BEGIN ATTACK
  cipher = matrix(vector((PC*(PH.inverse_mod(P2))).mod(P2)))
  R = (PP*(PH.inverse_mod(P2))).mod(P2)
  Rmat = getmultmatrix(R,P2,lenE)
  e1_candidate, e2_candidate = Prange(Rmat,cipher,lenE)
  print(f'Message recovery  E_1: {E1 == P(list(e1_candidate[0]))}      E_2: {E2 == P(list(e2_candidate[0]))}')
  timer.stop()
  time += timer.walltime
  
print(f'Average recovery time : {time/50}')

#sol = Rmat.solve_left(vector(lz))
#print(P(list(sol)) == PI.mod(P2))
