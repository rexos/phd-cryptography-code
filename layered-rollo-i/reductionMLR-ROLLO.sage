reset()
from sage.doctest.util import Timer
# parameters for modified Layered-ROLLO-I
# 128 bits
q, m, degPI, n1, n2 = 2,67,11,37,61
# 192 bits
#q, m, degPI, n1, n2 = 2,79,15,43,71
# 256 bits security
#q, m, degPI, n1, n2 = 2,97,20,53,103

# the following parameters describe max polynomial degrees
# this script uses vectorspaces to construct these polynomials
# so considering the constant term we need 1 entry more to get
# the correct bound on max degree.
degPI += 1
n1 += 1
n2 += 1

# Choices of P1 according to modified Layered-ROLLO-I implementation
# 128 bits
P1=x^37 + x^22 + x^14 + x^2 + 1
# 192 bits
#P1=x^43 + x^27 + x^22 + x^5 + 1
# 256 bits
#P1 = x^53 + x^50 + x^41 +x^20 + 1

Fqm = GF(q^m)
P.<x> = Fqm[]
F2x.<x> = GF(2)[]

def shift(v,W):
  newv = [0] + [v[i-1] for i in range(1,len(v))]
  scalar = v[-1]
  return W(newv), scalar
    
def vecpol(pol, l):
  deg = pol.degree()
  assert deg < l
  W = VectorSpace(Fqm, l)
  return W(list(pol) + [0 for i in range(l-deg-1)])
    
def xnmodpol(n,pol):
  assert pol.is_monic()
  d = pol.degree()
  W = VectorSpace(Fqm, d)
  if n < d:
    return vecpol(x^n, d)
  else:
    Q = W(list(pol)[:-1])
    prev = Q
    for i in range(1,n-d+1):
      shifted, scalar = shift(prev, W)
      toadd = scalar*Q
      prev = shifted + toadd
    return prev

def getmultmatrix(B,pol):
  Bcoeff = list(B)
  nrows = degPI
  ncols = 2*n2 - 1
  vec = vecpol(B, ncols)
  N = [vec]
  for i in range(1,nrows):
    vec, _ = shift(vec, VectorSpace(Fqm, ncols))
    N.append(vec)
    
  N = matrix(N)
  leftN = N[:,:n2]
  for i in range(1,nrows):
    for j in range(-i,0):
      toadd = Bcoeff[j]*xnmodpol(n2+(i+j), pol)#vecpol((x^(n2+i+j)).mod(pol),n2)
      leftN[i] += toadd
  
  return leftN

V = VectorSpace(Fqm,n1)
u,v = V.random_element(), V.random_element()
Pu, Pv = P(list(u)), P(list(v))

# Pick a random irreducible P2 over F2. Might as well be taken over F_{2^m}. 
P2 = F2x.irreducible_element(n2)
P1 = P(P1)
P2 = P(P2)

P2coeff = list(P2)
#PI = P(list(VectorSpace(Fqm,degPI).random_element()))
# PI is a polynomial of degree exctly degPI (-1 because I increased it at the beginning of the script)
PI = P.random_element(degPI - 1)
PO = P(list(VectorSpace(Fqm,n2).random_element()))
xy = (Pu.inverse_mod(P1)*Pv).mod(P1)
z = (PI*xy).mod(P1)

PP, PH = (PO*PI).mod(P2), (PO*z).mod(P2)

timer = Timer()
timer.start()
R = (PH*(PP.inverse_mod(P2))).mod(P2)

Rmat = getmultmatrix(R,P2)
M = Rmat[:,n2-degPI+1:]

ker = M.left_kernel()
i=1
while ker.dimension() > 1:
  print('taking an extra column..')
  M = Rmat[:,n2-degPI+1-i:]
  ker = M.left_kernel()
  i += 1

lamPI = P(list(ker.basis()[0]))
lamPO = (PP * (lamPI.inverse_mod(P2))).mod(P2)
lamz = (PH * (lamPO.inverse_mod(P2))).mod(P2)
key = (lamz * (lamPI.inverse_mod(P1))).mod(P1)
timer.stop()  
print(f'found key matches real y/x : {key == xy} in {timer.walltime}')  
