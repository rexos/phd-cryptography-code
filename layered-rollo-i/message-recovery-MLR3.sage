reset()
from sage.doctest.util import Timer

# parameters for modified Layered-ROLLO-I
# 128 bits
#q, m, degPI, n1, n2, na = 2,67,37,37,61,4
# 192 bits
#q, m, degPI, n1, n2, na = 2,79,43,43,71,4
# 256 bits security
q, m, degPI, n1, n2, na = 2,97,53,53,103,4

# Choices of P1 according to modified Layered-ROLLO-I implementation
# WE DO NOT CARE WHAT P1 IS. MIGHT AS WELL BE RANDOM.
# 128 bits
#P1=x^37 + x^22 + x^14 + x^2 + 1
# 192 bits
#P1=x^43 + x^27 + x^22 + x^5 + 1
# 256 bits
P1 = x^53 + x^50 + x^41 +x^20 + 1


lenE = n2 - n1 - na - 1
degE = lenE-1
print(degE)

Fqm = GF(q^m)
P.<x> = Fqm[]
F2x.<x> = GF(2)[]

def getmultmatrix(R,P2,nrows):
  M = []
  for i in range(n2):
    el = list((R*x^i).mod(P2))
    M.append(el + [0 for j in range(n2-len(el))])
  M = matrix(Fqm,M)
  return M[:nrows,:]

def findcommoninv(M,N,cipher):
  k,n = M.dimensions()
  p = list(range(lenE+1,n))
  while True: 
    shuffle(p)
    indexes = p[:k]
    indexes.sort()
    colsM = [M.columns()[i] for i in indexes]
    colsN = [N.columns()[i] for i in indexes]
    M1 = matrix(Fqm, colsM)
    N1 = matrix(Fqm, colsN)
    if M1.is_invertible() and N1.is_invertible():
      return M1.transpose(),N1.transpose(),vector([cipher[i] for i in indexes])

V = VectorSpace(Fqm,n1)
u,v = V.random_element(), V.random_element()
Pu, Pv = P(list(u)), P(list(v))

P2 = F2x.irreducible_element(n2)
P1 = P(P1)
P2 = P(P2)
PI = P.random_element(degPI)
PO = P(list(VectorSpace(Fqm,n2+1).random_element()))
PNA = P.random_element(na)
xy = (Pu.inverse_mod(P1)*Pv).mod(P1)
z = (PI*xy).mod(P1)
lz = list(z) + [0 for j in range(0,n2-len(list(z)))]
#PP, PH = (PO*PI).mod(P2), (PO*z).mod(P2)

time = 0
timer = Timer()
for i in range(50):
  E1 = P.random_element(degE)
  E2 = P.random_element(degE)
  PNC = P.random_element(degE)
  PNB = P.random_element(na)
  #### PUBLIC DATA
  PP, PH = (PO*(PI + PNA*P1)).mod(P2), (PO*z).mod(P2)
  PB = (PO*PNB*P1).mod(P2)
  PC = (PP*E1 + PH*E2 + PB*PNC).mod(P2)

  print('Begin ATTACK')
  timer.start()
  #### BEGIN ATTACK
  s1 = vector((PC*(PB.inverse_mod(P2))).mod(P2))
  s2 = vector((PC*(PH.inverse_mod(P2))).mod(P2))
  s3 = vector((PC*(PP.inverse_mod(P2))).mod(P2))

  A1 = (PP*(PB.inverse_mod(P2))).mod(P2)
  B1 = (PH*(PB.inverse_mod(P2))).mod(P2)
  A1mat = getmultmatrix(A1,P2,lenE)
  B1mat = getmultmatrix(B1,P2,lenE)
  A1bar,B1bar,s1bar = findcommoninv(A1mat,B1mat,s1)
  
  A2 = (PP*(PH.inverse_mod(P2))).mod(P2)
  C2 = (PB*(PH.inverse_mod(P2))).mod(P2)
  A2mat = getmultmatrix(A2,P2,lenE)
  C2mat = getmultmatrix(C2,P2,lenE)
  A2bar,C2bar,s2bar = findcommoninv(A2mat,C2mat,s2)

  B3 = (PH*(PP.inverse_mod(P2))).mod(P2)
  C3 = (PB*(PP.inverse_mod(P2))).mod(P2)
  B3mat = getmultmatrix(B3,P2,lenE)
  C3mat = getmultmatrix(C3,P2,lenE)
  B3bar,C3bar,s3bar = findcommoninv(B3mat,C3mat,s3)

  Sys = C3bar*B3bar.inverse() + C2bar*A2bar.inverse()*A1bar*B1bar.inverse()
  val = s2bar*A2bar.inverse()*A1bar*B1bar.inverse() - s1bar*B1bar.inverse() + s3bar*B3bar.inverse()
  z1 = Sys.solve_left(val)
  x1 = (s2bar - z1*C2bar)*A2bar.inverse()
  y1 = (s3bar - z1*C3bar)*B3bar.inverse()
  print(f'Message recovery  E_1: {E1 == P(list(x1))}      E_2: {E2 == P(list(y1))}    PNC: {PNC == P(list(z1))}')
  timer.stop()
  time += timer.walltime
  
print(f'Average recovery time : {time/50}')