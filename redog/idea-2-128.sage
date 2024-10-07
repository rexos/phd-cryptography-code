# AGHT: Aragon, Gaborit, Hauteville, Tilich
# GRS: main case in Gaborit, Ruatta, Schrek
# fast: fast case from Gaborit, Ruatta, Schrek 
# BBB: Bardet, Briaud, Bros, Gaborit, Neiger, Ruatta, Tillich,
# BBC: Bardet, Bros, Cabarcas, Gaborit, Perlner, Smith-Tone, Tillich, Verbel
# BBB23 Bardet, Briaud, Bros, Gaborit, Tillich corrects BBC + add new attack
# brute: brute-force search as in paper

q=2
w_win = 2.37
w_stras = 2.807

# to speed up repeated binomial calculations, remember the values

limit = 100000
sys.setrecursionlimit(limit)

from collections.abc import Hashable

class memoized(object):
  def __init__(self,func):
    self.func = func
    self.cache = {}
    self.__doc__ = '   [memoized.memoized wrapper around the following:]\n'
    if func.__doc__ != None:
      self.__doc__ += func.__doc__
    self.__wrapped__ = func
  def __call__(self,*args):
    if not isinstance(args,Hashable):
      return self.func(*args)
    if not args in self.cache:
      self.cache[args] = self.func(*args)
    return self.cache[args]

@memoized
def factorial_cached(a):
  assert a >= 0
  assert a < limit
  if a == 0: return 1
  if a > 4*n: return factorial(a)
  return a*factorial_cached(a-1)

@memoized
def binomial_cached(a,b):
  assert a < limit
  a = ZZ(a)
  assert a >= 0
  b = ZZ(b)
  if b < 0: return 0
  if b > a: return 0
  return factorial_cached(a)/(factorial_cached(b)*factorial_cached(a-b))

# for some large inputs in brute want to skip memorizing
binomial_raw = binomial
binomial = binomial_cached

def log2(x):
	assert x > 0
	return log(RR(x),2.0)


def A_b(NF,RF,MF,KF,b):
	return sum(binomial(NF,RF)*binomial(MF*KF + 1,j) for j in range(1,b+1))

def B_b(NF,RF,MF,KF,b):
	return sum(MF*binomial(NF - KF - 1,RF)*binomial(MF * KF + 1,j) for j in range(1,b+1))

def C_b(NF,RF,MF,KF,b):
	return sum(sum((-1)^(s+1) * binomial(NF, RF+s) * binomial(MF + s - 1, s) * binomial(MF * KF + 1, j - s) for s in range(1,j + 1)) for j in range(1, b + 1))

def D_b(NF,RF,MF,KF,b):
	return  (B_b(NF,RF,MF,KF,b)*binomial(KF + RF + 1, RF) + C_b(NF,RF,MF,KF,b)*(MF * KF + 1)*(RF + 1))/(B_b(NF,RF,MF,KF,b) + C_b(NF,RF,MF,KF,b))

def N_bq(NF,RF,MF,KF,b):
        return  (N_bqm(NF,RF,MF,KF,b) - N_bqsyz(NF,RF,MF,KF,b))

def N_bqm(NF,RF,MF,KF,b):
        return (sum(binomial(NF - s, RF)*binomial(KF + b - 1 - s, b - 1)  for s in range(1,KF + 1)) - binomial(NF - KF - 1, RF)*binomial(KF + b - 1, b))


def N_bqsyz(NF,RF,MF,KF,b):
        return (MF - 1) * sum((-1)^(s+1)*binomial(KF + b - s - 1, b - s)*binomial(NF - KF - 1, RF + s) for s in range(1,b+1))

def M_b(NF,RF,MF,KF,b):
        return binomial(KF + b - 1,b)*(binomial(NF,RF) - MF*binomial(NF - KF -1, RF))

# level 128
#n = 44; k =  8; l = 37; m =  83; r = 18; lam = 3; t = 6

# level 192
#n = 58; k = 10; l = 49; m = 109; r = 24; lam = 3; t = 8

# level 256
n = 72; k = 12; l = 61; m = 135; r = 30; lam = 3; t = 10


K = l; M = m

AGHT = []; GRS = []; fast = []; BBB_win = []; BBB_stras = [] 
BBC_win = []; BBC_stras = []; BBC_wied = []; BBB23_win = []; BBB23_stras = [] ; brute = []

for t2 in range((r//lam) + 1): # we can handle brute-force attacks 
	t1 = r - t2 * lam
	N = K + min(t1,t2)
	# initializing all values  (counter, cost, and direction)
	i_AGHT = 0; i_GRS = 0; i_fast = 0; i_BBB_win = 0; i_BBB_stras = 0; 
	i_BBC_win = 0; i_BBC_stras = 0; i_BBC_wied = 0; i_BBB23_win = 0; i_BBB23_stras = 0;
	c_AGHT = oo; c_GRS = oo; c_fast = oo; c_BBB_win = oo; c_BBB_stras = oo; 
	c_BBC_win = oo; c_BBC_stras = oo; c_BBC_wied = oo; c_BBB23_win = oo; c_BBB23_stras = oo;
	dir_AGHT = 'l'; dir_GRS = 'l'; dir_fast = 'l'; dir_BBB_win = 'l'; dir_BBB_stras = 'l'; 
	dir_BBC_win = 'l'; dir_BBC_stras = 'l'; dir_BBC_wied = 'l'; dir_BBB23_win = 'l'; dir_BBB23_stras = 'l';  
	# first we look from the left
	for i in range (2*n - k - N + 1):
		# we normally get rank s taking s < t columns
		if (N + i) in range(K + t1, n+1): R = t1 # purely in c1 part, only rank t1
		elif (N + i) >= n + t2: R = t1 + t2 # reached full rank
		elif (N + i) < K + t1: continue # not enough information to decode
		else: R = t1 + N + i - n # taking N + i - n columns from right part
		try:
			if (R*(K+1)*M/(N+i) -M) >= 0:
				cost = log2((N + i -K)^w_stras*M^w_stras*q^(R*(K+1)*M/(N+i) -M))
				if cost < c_AGHT: c_AGHT = cost; i_AGHT = N + i; dir_AGHT = 'l'
		except:
			pass
		try:
			if R > 0:
				cost = log2((N+i-K)^w_stras*M^w_stras*q^(min(R*floor(K*M/(N+i)),(R-1)*floor((K+1)*M/(N+i)))))
				if cost < c_GRS: c_GRS = cost; i_GRS = N + i; dir_GRS = 'l'
		except:
			pass
		if R > 0:
			if K > ceil(((R+1)*(K+1)-(N+i)-1)/R) and ceil(((R+1)*(K+1)-(N+i)-1)/R) >= 0: 
				try:
					cost = log2(R^w_stras * K^w_stras * q^(R*ceil(((R+1)*(K+1)-(N+i)-1)/R)))
					if cost < c_fast: c_fast = cost; i_fast = N + i; dir_fast = 'l'
				except:
					pass
		if (N + i - K - 1) > R and M*binomial((N+i) - K - 1, R) + 1 >= binomial((N+i), R): 
			try:
				cost = log2(((((M+N+i)*R)^R)/factorial(R))^w_win) 
				if cost < c_BBB_win: c_BBB_win = cost; i_BBB_win = N + i; dir_BBB_win = 'l'
			except:
				pass
			try:
				cost = log2(M*binomial((N+i) - K - 1, R) * binomial((N+i), R)^(w_win-1))
				if cost < c_BBC_win: c_BBC_win = cost; i_BBC_win = N + i; dir_BBC_win = 'l overdetermined'
			except:
				pass
			try:
				cost = log2(((((M+N+i)*R)^R)/factorial(R))^w_stras) 
				if cost < c_BBB_stras: c_BBB_stras = cost; i_BBB_stras = N + i; dir_BBB_stras = 'l'
			except:
				pass
			try:
				cost = log2(M*binomial((N+i) - K - 1, R) * binomial((N+i), R)^(w_stras-1))
				if cost < c_BBC_stras: c_BBC_stras = cost; i_BBC_stras = N + i; dir_BBC_stras = 'l overdetermined'
			except:
				pass
		else: 
			try:
				cost  =  log2(((((M+N+i)*R)^(R+1))/factorial(R+1))^w_win) 
				if cost < c_BBB_win: c_BBB_win = cost; i_BBB_win = N + i; dir_BBB_win = 'l'
			except:
				pass
			try:
				cost =  log2(((((M+N+i)*R)^(R+1))/factorial(R+1))^w_stras) 
				if cost < c_BBB_stras: c_BBB_stras = cost; i_BBB_stras = N + i; dir_BBB_stras = 'l'
			except:
				pass
			j = 1
			if (N + i - K -1) >= R:
				while (M*binomial((N+i) - K - 1, R) + 1 < binomial((N+i-j),R)): j = j+1
				if min(N + i-K - 1, N + i -j) >= R:
					try:
						cost = log2(q^(j*R)*M*binomial((N+i) - K - 1, R)*binomial((N+i-j), R)^(w_win-1))
						if cost < c_BBC_win: c_BBC_win = cost; i_BBC_win = N + i; dir_BBC_win = 'l hybrid'
					except:
						pass
					try:
						cost = log2(q^(j*R)*M*binomial((N+i) - K - 1, R)*binomial((N+i-j), R)^(w_stras-1))
						if cost < c_BBC_stras: c_BBC_stras = cost; i_BBC_stras = N + i; dir_BBC_stras = 'l hybrid'
					except:
						pass
			b = 1
			while (A_b(N+i,R,M,K,b) - 1) > C_b(N+i,R,M,K,b)  and b < R + 2:
				b = b + 1
			if b < R+2:
				try:		
					cost = log2((K*M + 1) * (R+1)*(A_b(N+i,R,M,K,b))^2)
					if cost < c_BBC_wied: c_BBC_wied = cost; i_BBC_wied = N + i; dir_BBC_wied = 'l 26, 27'
				except:
					pass
# removed part of BBC23 which BBGT shows not to be valid

			# formulas from BBBGT
			a = 0
			while a * R < c_BBB23_stras and a < K and K < N + i:
				b = 1
				while N_bq(N+i-a,R,M,K-a,b) < (M_b(N+i-a,R,M,K-a,b) -1) and b < (N + i): b = b + 1
				if N_bq(N+i-a,R,M,K-a,b) >= M_b(N+i-a,R,M,K-a,b) -1 and N_bq(N+i-a,R,M,K-a,b) > 0 and  M_b(N+i-a,R,M,K-a,b) > 0:
					try:
						cost = a*R + log2(((N_bq(N+i-a,R,M,K-a,b)* M_b(N+i-a,R,M,K-a,b)^(w_win - 1))))	
						if cost < c_BBB23_win: c_BBB23_win = cost;i_BBB23_win = i; dir_BBB23_win = ['l',a,b]
					except:
						pass
					try:
						cost = a*R + log2(((N_bq(N+i-a,R,M,K-a,b)* M_b(N+i-a,R,M,K-a,b)^(w_stras - 1))))
						if cost < c_BBB23_stras: c_BBB23_stras = cost;  i_BBB23_stras = i; dir_BBB23_stras = ['l',a,b]
					except:
						pass
				a = a + 1




	# now do the right part
	# no new initialization, so 'l' has some priority
	for i in range (2*n - k - N + 1):
		# we normally get rank s taking s < t columns
		if (N + i) in range(K + t2, n - k + 1): R = t2 # this case is empty for the REDOG parameters
		elif (N + i) >= n - k + t1: R = t1 + t2 # reached full rank
		# all other cases are empty for REDOG
		elif (N + i) < K + t2: continue # not enough information to decode
		else: 
			if (N + i) > (K + t2 + N + i - (n - k)) : R = t2 + N + i - (n - k)
			else: continue
		try:
			if (R*(K+1)*M/(N+i) -M) >= 0:
				cost = log2((N + i -K)^w_stras*M^w_stras*q^(R*(K+1)*M/(N+i) -M))
				if cost < c_AGHT: c_AGHT = cost; i_AGHT = N + i; dir_AGHT = 'r'
		except:
			pass
		try:
			if R > 0: 
				cost = log2((N+i-K)^w_stras*M^w_stras*q^(min(R*floor(K*M/(N+i)),(R-1)*floor((K+1)*M/(N+i)))))
				if cost < c_GRS: c_GRS = cost; i_GRS = N + i; dir_GRS = 'r'
		except:
			pass
		if R > 0:
			if K > ceil(((R+1)*(K+1)-(N+i)-1)/R) and ceil(((R+1)*(K+1)-(N+i)-1)/R) >= 0: 
				try:
					cost = log2(R^w_stras * K^w_stras * q^(R*ceil(((R+1)*(K+1)-(N+i)-1)/R)))
					if cost < c_fast: c_fast = cost; i_fast = N + i; dir_fast = 'r'
				except:
					pass
		if (N + i - K - 1) >= R and M*binomial((N+i) - K - 1, R) + 1 >= binomial((N+i), R): 
			try:
				cost = log2(((((M+N+i)*R)^R)/factorial(R))^w_win) 
				if cost < c_BBB_win: c_BBB_win = cost; i_BBB_win = N + i; dir_BBB_win = 'r'
			except:
				pass
			try:
				cost = log2(M*binomial((N+i) - K - 1, R) * binomial((N+i), R)^(w_win-1))
				if cost < c_BBC_win: c_BBC_win = cost; i_BBC_win = N + i; dir_BBC_win = 'r overdetermined'
			except:
				pass
			try:
				cost = log2(((((M+N+i)*R)^R)/factorial(R))^w_stras) 
				if cost < c_BBB_stras: c_BBB_stras = cost; i_BBB_stras = N + i; dir_BBB_stra = 'r'
			except:
				pass
			try:
				cost = log2(M*binomial((N+i) - K - 1, R) * binomial((N+i), R)^(w_stras-1))
				if cost < c_BBC_stras: c_BBC_stras = cost; i_BBC_stras = N + i; dir_BBC_stras = 'r overdetermined'
			except:
				pass
		else: 
			try:
				cost  =  log2(((((M+N+i)*R)^(R+1))/factorial(R+1))^w_win) 
				if cost < c_BBB_win: c_BBB_win = cost; i_BBB_win = N + i; dir_BBB_win = 'r'
			except:
				pass
			try:
				cost =  log2(((((M+N+i)*R)^(R+1))/factorial(R+1))^w_stras) 
				if cost < c_BBB_stras: c_BBB_stras = cost; i_BBB_stras = N + i; dir_BBB_stras = 'r'
			except:
				pass
			j = 1
			if (N + i - K -1) >= R:
				while (M*binomial((N+i) - K - 1, R) + 1 < binomial((N+i-j),R)): j = j+1
				if min(N + i-K - 1, N + i -j) >= R:
					try:
						cost = log2(q^(j*R)*M*binomial((N+i) - K - 1, R)*binomial((N+i-j), R)^(w_win-1))
						if cost < c_BBC_win: c_BBC_win = cost; i_BBC_win = N + i; dir_BBC_win = 'r hybrid'
					except:
						pass
					try:
						cost = log2(q^(j*R)*M*binomial((N+i) - K - 1, R)*binomial((N+i-j), R)^(w_stras-1))
						if cost < c_BBC_stras: c_BBC_stras = cost; i_BBC_stras = N + i; dir_BBC_stras = 'r hybrid'
					except:
						pass
			b = 1
			while (A_b(N+i,R,M,K,b) - 1) > C_b(N+i,R,M,K,b)  and b < R + 2:
				b = b + 1
			if b < R+2:
				try:		
					cost = log2((K*M + 1) * (R+1)*(A_b(N+i,R,M,K,b))^2)
					if cost < c_BBC_wied: c_BBC_wied = cost; i_BBC_wied = N + i; dir_BBC_wied = 'r 26 , 27'
				except:
					pass
# removed part of BBC because BBGT shows that it not valid

			# formulas from BBBGT
			a = 0
			while a * R < c_BBB23_stras and a < K and K < N + i:
				b = 1
				while N_bq(N+i-a,R,M,K-a,b) < (M_b(N+i-a,R,M,K-a,b) -1) and b < (N + i): b = b + 1
				if N_bq(N+i-a,R,M,K-a,b) >= M_b(N+i-a,R,M,K-a,b) -1 and N_bq(N+i-a,R,M,K-a,b) > 0 and  M_b(N+i-a,R,M,K-a,b) > 0:
					try:
						cost = a*R + log2(((N_bq(N+i-a,R,M,K-a,b)* M_b(N+i-a,R,M,K-a,b)^(w_win - 1))))	
						if cost < c_BBB23_win: c_BBB23_win = cost;i_BBB23_win = i; dir_BBB23_win = ['l',a,b]
					except:
						pass
					try:
						cost = a*R + log2(((N_bq(N+i-a,R,M,K-a,b)* M_b(N+i-a,R,M,K-a,b)^(w_stras - 1))))
						if cost < c_BBB23_stras: c_BBB23_stras = cost;  i_BBB23_stras = i; dir_BBB23_stras = ['l',a,b]
					except:
						pass
				a = a + 1


	AGHT.append((c_AGHT, i_AGHT, dir_AGHT))
	GRS.append((c_GRS, i_GRS, dir_GRS))
	fast.append((c_fast, i_fast, dir_fast))
	BBB_win.append((c_BBB_win, i_BBB_win, dir_BBB_win))
	BBB_stras.append((c_BBB_stras, i_BBB_stras, dir_BBB_stras))
	BBC_win.append((c_BBC_win, i_BBC_win, dir_BBC_win))
	BBC_stras.append((c_BBC_stras, i_BBC_stras, dir_BBC_stras))
	BBC_wied.append((c_BBC_wied, i_BBC_wied, dir_BBC_wied))
	BBB23_win.append((c_BBB23_win, i_BBB23_win, dir_BBB23_win))
	BBB23_stras.append((c_BBB23_stras, i_BBB_stras, dir_BBB23_stras))
	brutel = log2(binomial_raw(q^m - 1, t1)* q^(t1*l)/(q-1)^t1)	
	bruter = log2(q^m * binomial_raw(q^m - 1, t2)* q^(t2*(l-1))/(q-1)^t2)
	if brutel <= bruter: brute.append((brutel,0,'l'))
	else: brute.append((bruter,0,'r'))

algos = [AGHT,GRS,fast,BBB_win,BBB_stras,BBC_win,BBC_stras,BBC_wied,BBB23_win,BBB23_stras,brute]
algo_names = ['AGHT','GRS','fast','BBB_win','BBB_stras','BBC_win','BBC_stras','BBC_wied','BBB23_win','BBB23_stras','brute']

best = []
for i in range((r//lam)+ 1):
	local = [x[i] for x in algos]
	best.append((min(local),algo_names[local.index(min(local))]))

print('best attack per position')

print(best)
print(' ')
print(' ')

print('best parameter choices have attack costs', max(best), 'at t2 = ', best.index(max(best)))
print(' ')
print(' ')

print('Updated choice in REDOG has:' )

t2 = r//(2*lam)

for i in range(len(algos)):
	print(algo_names[i], ': ', algos[i][t2])

algos_short = [BBB_stras,BBC_stras,BBB23_stras,brute]
algos_short_names = ['BBB_stras','BBC_stras','BBB23_stras','brute']
realistic = []
for i in range((r//lam)+ 1):
    local = [x[i] for x in algos_short]
    realistic.append((min(local),algos_short_names[local.index(min(local))]))
print(realistic)
print('best option using Strassen has security ',max(realistic), 'at t2 =', realistic.index(max(realistic)))

