#TROVO I MINIMI PER I PUNTI ROSSI

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


def test(k,w_u,w_f,w_c,w_e):
	u = sample(range(k), w_u)  # sample u poly
	f = sample(range(k), w_f)  # sample f poly
	c = sample(range(k), w_c)  # sample c polynomial
	e = sample(range(k), w_e)  # sample e polynomial

	##compute s = u f + c e
	uf = sparse_mul(u, f, k)
	ce = sparse_mul(c, e, k)
	s = np.mod([i+j for i,j in zip(uf,ce)],2)


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
	
	return corr_values_0, corr_values_1

##########################################################################################

k = 12539
n = 2 * k
w_u = 33
w_f = 145
w_c = 31
w_e = 141

min_sum = 0
max_sum = 0

for i in range(1000):
	print(i)
	corr_values_0, corr_values_1 = test(k,w_u,w_f,w_c,w_e)
	
	max_loc = max(corr_values_0)
	min_loc = min(corr_values_1) 
	
	max_sum += max_loc
	min_sum += min_loc

	max_mean = max_sum / (i+1) * 1.
	min_mean = min_sum / (i+1) * 1.
	print("Minimo valore di correlazione per 1", min_mean)
	print("Massimo valore di correlazione per 0", max_mean)

# plt.scatter(pos_0, corr_values_0, color='b')
# plt.scatter(pos_1, corr_values_1, color='r')
# plt.legend(['0 coeff in y', '1 coeff in y'])
# plt.grid(True)
# plt.show()
