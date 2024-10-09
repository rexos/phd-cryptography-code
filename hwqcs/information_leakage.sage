

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


# Parameters for 128 bit of security
# k = 12539
# n = 2 * k
# w_u = 33
# w_f = 145
# w_c = 31
# w_e = 141

# Parameters for 192 bit of security
# k = 18917
# n = 2 * k
# w_u = 41
# w_f = 185
# w_c = 39
# w_e = 177

# Parameters for 256 bit of security
k = 25417
n = 2 * k
w_u = 51
w_f = 201
w_c = 51
w_e = 191


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
    

plt.scatter(pos_0, corr_values_0, color='b')
plt.scatter(pos_1, corr_values_1, color='r')
plt.legend(['0 coeff in y', '1 coeff in y'])
plt.grid(True)
plt.show()

    

fileName1 = "corr1.dat"
with open(fileName1, "w") as f:
	f.write("x y\n")
	for i in range(len(pos_1)):
		f.write(str(pos_1[i]) + " " + str(corr_values_1[i]) + "\n")
f.close()

#stampo anche i valori per corr_0, però non posso prenderne troppi altrimenti latex si impunta a stamparli

numberofSamples = len(pos_1) * 10
samples = sample(range(len(pos_0)), numberofSamples)  # sample u poly
sampled_pos_0 = [pos_0[i] for i in samples]
sampled_corr_values_0 = [corr_values_0[i] for i in samples ]

fileName0 = "corr0.dat"
with open(fileName0, "w") as f:
	f.write("x y\n")
	for i in range(len(sampled_pos_0)):
		f.write(str(sampled_pos_0[i]) + " " + str(sampled_corr_values_0[i]) + "\n")
f.close()
