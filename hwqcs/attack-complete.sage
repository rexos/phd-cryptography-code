# Level 128
k,wf,wu,we,wc,ws,wt,tau = 12539,145,33,141,31,4844,4937,12

# Level 192
#k,wf,wu,we,wc,ws,wt,tau = 18917,185,41,177,39,7450,7592,15

# Level 256
#k,wf,wu,we,wc,ws,wt,tau = 25417,145,51,191,51,10111,10216,21


F = GF(2)
R1.<y> = F[]
R.<x> = R1.quo(y^k - 1)

def weight(v):
	return sum(1 for i in v if i==1)

def keygen():
	f = []
	for i in range(2):
		inv = False
		while not inv:
			P = Permutations(k)
			p = P.random_element()
			meta_pol = [1 for i in range(wf)] + [0 for i in range(k-wf)]
			meta_pol = [meta_pol[p[i]-1] for i in range(k)]
			fi = R(meta_pol)
			inv = fi.is_unit()
		f += [fi]

	return f[0].inverse_of_unit()*f[1], f
	

def sign(H,sk):
	while True:
		e = []
		u = []
		P = Permutations(k)
		for i in range(2):
			p = P.random_element()
			ei = [1 for i in range(we)] + [0 for i in range(k-we)]
			ei = [ei[p[i]-1] for i in range(k)]	
			e += [ei]
		for i in range(2):
			p = P.random_element()
			ui = [1 for i in range(wu)] + [0 for i in range(k-wu)]
			ui = [ui[p[i]-1] for i in range(k)]	
			u += [ui]
		e = vector(e[0]+e[1])
		b = H*e

		p = P.random_element()
		c = [1 for i in range(wc)] + [0 for i in range(k-wc)]
		c = [c[p[i]-1] for i in range(k)]	
		s = [R(u[i])*sk[i]+ R(c)*R(list(e)[k*i:k*(i+1)]) for i in range(2)]
		if weight(s[1]) <= ws and weight(s[0]) <= ws and weight(R(u[0])*sk[1] + R(u[1])*sk[0]) <= wt:
			return s,b,c,e
			
		
for i in range(30):	
	pk,sk = keygen()
	print("computing public matrix, might take a while ...")
	h1 = matrix.circulant(list(pk))
	H = h1.augment(h1.inverse())
	print("done")
	mins = []
	broken = False
	count = 1;
	while not broken:
		print(f"generate one signature and analyze it ... {count}")
		count +=1
		s,b,c,e = sign(H,sk)
		c = R1(c)
		stats0 = [ZZ(0)]*k
		stats1 = [ZZ(0)]*k
		p0s0=[]
		p1s0=[]
		p0s1=[]
		p1s1=[]
		for m in c.monomials():
			v = m.degree()
			s0v = s[0]*x^(k-v)
			s1v = s[1]*x^(k-v)
			ls0 = list(s0v)
			ls1 = list(s1v)
			for i in range(k):
				stats0[i] += ZZ(ls0[i])
				stats1[i] += ZZ(ls1[i])

		s0zeros = []
		s0ones = []
		s1zeros = []
		s1ones = []
		for i in range(k):
			if e[i] == 0:
				p0s0 += [i]
				s0zeros += [stats0[i]]
				
			else:
				p1s0 += [i]
				s0ones += [stats0[i]]
				
			if e[k+i] == 0:
				p0s1 += [i]
				s1zeros += [stats1[i]]
				
			else:
				p1s1 += [i]
				s1ones += [stats1[i]]
		
		

		z0 = [i for i in range(k) if stats0[i]<tau]
		#print(len(z0),min(s0ones),len([i for i in s0ones if i<=tau]))

		z1 = [k+i for i in range(k) if stats1[i]<tau]
		#print(len(z1),min(s1ones),len([i for i in s1ones if i<=tau]))

		z013 = [i for i in range(k) if stats0[i]==tau]

		z113 = [k + i for i in range(k) if stats1[i]==tau]

		
		if True:
			#print("Start searching for an invertible submatrix")
			Htmp = zero_matrix(k)
			#print("guess some/other columns to exclude on the left and on the right...")
			s0smpcoord = sample(range(len(z013)), ceil(k/2)-len(z0))
			s0smp = [z013[i] for i in s0smpcoord]
			cols0 = z0 + s0smp
			s1smpcoord = sample(range(len(z113)), k-ceil(k/2)-len(z1))
			s1smp = [z113[i] for i in s1smpcoord]
			cols = cols0 + z1 + s1smp
			skip = False
			for i in cols:
				if e[i] == 1:
					#print("Unlucky", i)
					skip = True
			if skip: continue
			
			#print(len(z0), len(s0smp), len(z1),len(s1smp))
			sel = [i for i in range(2*k) if i not in cols]
			#print("build the submatrix ...")
			Htmp = H[:,sel]
			#print(f'Matrix is invertible : {Htmp.rank()==k}')
			if Htmp.rank() != k : continue
			#print("Computing error vector...")
			etmp = Htmp.inverse()*b
			erec = [0]*(2*k)
			for i in range(k):
				erec[sel[i]] = etmp[i]
			broken = vector(erec) == e
			print(f'Found error vector is valid : {broken}')
			print("*"*50)
		
		