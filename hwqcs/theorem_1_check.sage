# Compute theoretical and experimental values for Theorem 1

reset()

from random import sample
import numpy as np
import matplotlib.pyplot as plt

def vectorSum(c,k):
	res = [0] * len(c)
	for i in range(len(c)):
		res[i] = c[i] + k
	return res

def sparse_mul(a, b, n):
	c = [0] * n
	for i in a:
		new_pos = [0] * (len(b))
		for j in range(len(b)):
			new_pos[j] = (b[j] + i) % n
			c[new_pos[j]] = (c[new_pos[j]] + 1) % 2
	return c

##########################################################################################

k = 12539
n = 2 * k
w_u = 33
w_f = 145
w_c = 31
w_e = 141

# Each z-th entry of x encodes P((d_i(x)_j=z) | (e_i)_j = 0)
xx = [0,0,0,0,0,0.005,0.013,0.029,0.054,0.086,0.118,0.141,0.146,0.132,0.105,0.074,0.046,0.025,0.012,0.005,0.001,0,0,0,0,0,0,0]
# Each z-th entry of y encodesa P((d_i(x)_j=z) | (e_i)_j = 1)
yy = [0,0,0,0,0,0,0,0,0,0,0,0.002,0.005,0.0123,0.025,0.0464,0.0746,0.105,0.132,0.145,0.140,0.118,0.086,0.054,0.029,0.013,0.005,0.001]

xxx = [(idx, x) for idx, x in enumerate(xx)]
yyy = [(idy, y) for idy, y in enumerate(yy)]

# Experimental estimate of the probabilities 
u = sample(range(k), w_u)  # sample u poly
f = sample(range(k), w_f)  # sample f poly
c = sample(range(k), w_c)  # sample c polynomial
e = sample(range(k), w_e)  # sample e polynomial

##compute s = u f + c e
uf = sparse_mul(u, f, k)
ce = sparse_mul(c, e, k)
s = np.mod([i+j for i,j in zip(uf,ce)],2)

# Create the vectors that take into account the number of occurrences z for which d_i(x)_j=z, distinguishing e_ij = 0 and e_ij=1
pos_0 = []
corr_values_0 = []
pos_1 = []
corr_values_1 = []

for i in range(k):
	shifted_c_support = np.mod(vectorSum(c,i),k); # shift of c by 0,1,2,3,...
	corr_val = 0
	for j in range(len(shifted_c_support)):
		corr_val = corr_val + s[shifted_c_support[j]]
	if (i not in e): #if e_i == 0
		pos_0.append(i) # take note of i s.t. e_i==0
		corr_values_0.append(corr_val) # take note of corr_values
	else:
		pos_1.append(i)
		corr_values_1.append(corr_val)
	
# Compute the probability of having observed this phenomenon
number_of_tries_1 = w_e
number_of_tries_0 = k-w_e
d_values_for_0 = zero_vector(w_c+1)
d_values_for_1 = zero_vector(w_c+1)
prob_0 = []
prob_1 = []

for i in range(k-w_e):
	d_values_for_0[corr_values_0[i]] += 1
for i in range(len(d_values_for_0)):
	prob_0.append(d_values_for_0[i] / number_of_tries_0 * 1.)

for i in range(w_e):
	d_values_for_1[corr_values_1[i]] += 1
for i in range(len(d_values_for_1)):
	prob_1.append(d_values_for_1[i] / number_of_tries_1 * 1.)


#Print
p1 = list_plot(list(xxx),color='red')
p11 = list_plot(list(prob_0),color='orange')
p2 = list_plot(list(yyy),color='blue')
p22 = list_plot(list(prob_1),color='teal')

p = p1+p11+p2+p22
p.show()