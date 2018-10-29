# implementation of SIDH with optimal strategies
# and Edwards arithmetic
#
# based on code from https://github.com/Microsoft/PQCrypto-SIDH
# by Costello, Longa, Naehrig (Microsoft Research)
# 



import cProfile, pstats, StringIO
from random import randint
pr = cProfile.Profile()
pr.enable()

#own class for complex numbers

class Complex(object):
	def __init__(self, real, imag=0):
		self.re = long(real)
		self.im = long(imag)
        
	def __add__(self, other):
		return Complex(self.re + other.re, self.im + other.im)

	def __sub__(self, other):
		return Complex(self.re - other.re, self.im - other.im)

	def __mul__(self, other):
		ab0=self.re*other.re
		ab1=self.im*other.im
		c=(self.re+self.im)*(other.re+other.im)
		return Complex((ab0-ab1)%p, (c-ab0-ab1)%p)


	def __neg__(self):  
		return Complex(-self.re, -self.im)

	def __eq__(self, other):
		return self.re == other.re and self.im == other.im

	def __ne__(self, other):
		return not self.__eq__(other)

	def __str__(self):
		return '(%u, %u)' % (self.re %p, self.im %p)

	def __repr__(self):
		return 'Complex' + str(self.re ,self.im)

	def __pow__(self, power): #only squares required
		return Complex(((self.re+self.im)*(self.re-self.im))%p, (2*self.im*self.re)%p)
		
	def __mod__(self, p):
		return Complex(self.re % p, self.im % p)	









####################################################################

def j_inv(A, C):  
	#input: parameters (A:C) of projective curve
	#output: j-invariant
	jinv = A**2  
	t1 = C**2
	t0 = t1 + t1
	t0 = jinv - t0
	t0 = t0 - t1
	jinv = t0 - t1
	t1 = t1**2
	jinv = jinv * t1
	t0 = t0 + t0
	t0 = t0 + t0
	t1 = t0**2
	t0 = t0 * t1
	t0 = t0 + t0
	t0 = t0 + t0
	jinv = inv(jinv)
	jinv = t0 * jinv

	return jinv   #cost: 3M+4S+8a+1I


###########################################################	


#function for Montgomery differential addition
def xADD(XP, ZP, XQ, ZQ, xPQ):
	#input: projective coordinates xP=XP/ZP and xQ=XQ/ZQ
	#       affine difference x(P-Q)=xPQ
	#output: projective coordinates x(Q+P)=XQP/XZP
	t0 = XP + ZP   
	t1 = XP - ZP
	XP = XQ - ZQ
	ZP = XQ + ZQ
	t0 = (XP * t0)%p
	t1 = (ZP * t1)%p
	ZP = t0 - t1
	XP = t0 + t1
	ZP = (ZP**2)%p
	XQP = (XP**2)%p
	ZQP = (xPQ * ZP)%p
	
	return XQP, ZQP    #cost: 3M+2S+6a	
		
		
##############################################################


#function for Montgomery doubling with projective curve constant
def xDBL(X, Z, A24, C24):
	#input: projective coordinates xP=X/Z
	#       curve constant A24/C24 = (A/C+2)/4
	#output: projective coordinates x(2P)=X2/Z2
	t0 = X - Z      #code from msr
	t1 = X + Z
	t0 = t0**2
	t1 = t1**2 
	Z2 = C24 * t0
	X2 = Z2 * t1
	t1 = t1 - t0
	t0 = A24 * t1
	Z2 = Z2 + t0
	Z2 = Z2 * t1
	
	return X2, Z2   #cost: 4M+2S+4a

########################################################

#Edwards-version of xDBL	
def edDBL(Y,Z,AE,DE):
	t0=Y**2
	t1=Z**2
	t2=t0+t1
	t2=t2**2
	t0=t0**2
	t1=t1**2
	t2=t2-t0
	t2=t2-t1
	Y2=t2*AE  #Y2=2a*Y^2Z^2
	t2=t2*DE  #t2=2d*Y^2Z^2
	t0=t0*DE  #t0=d*Y^4
	t1=t1*AE  #t1=a*Z^4
	t0=t0+t1  #t0=d*Y^4+a*Z^4
	Z2=t0-t2  #
	Y2=Y2-t0  #cost: 5S+4M

	return Y2,Z2

######################################################

#Edwards-version of xDBLe	
def edDBLe(XP,ZP,A,C,e):
	
	C2=C+C
	AE=A+C2
	DE=A-C2
	
	YeP = XP-ZP
	ZeP = ZP+XP
	
	for i in range(0,e):
		YeP, ZeP = edDBL(YeP, ZeP, AE, DE)
	
	XeP=YeP+ZeP
	ZeP=ZeP-YeP	
	return XeP, ZeP	                           #cost:4eM+5eS
			
###############################################################


#function for step in Montgomery ladder
#simultaneous doubling and differential addition
def xDBLADD(XP,ZP,XQ,ZQ,xPQ,A24):
	#input: projective coordinates xP=XP/ZP and xQ=XQ/ZQ, 
    #       affine difference x(P-Q)=xPQ and 
    #       curve constant A24=(A+2)/4.	
    #output: projective coordinates of x(2P)=X2P/Z2P
    #        and x(Q+P)=XQP/ZQP
    t0 = XP + ZP                  #code from msr
    t1 = XP - ZP 
    X2P = t0**2
    t2 = XQ - ZQ
    XQP = XQ + ZQ
    t0 = t0 * t2
    Z2P = t1**2
    t1 = t1 * XQP
    t2 = X2P - Z2P
    X2P = X2P * Z2P
    XQP = A24 * t2
    ZQP = t0 - t1
    Z2P = XQP + Z2P
    XQP = t0 + t1
    Z2P = Z2P * t2
    ZQP = ZQP**2
    XQP = XQP**2
    ZQP = xPQ * ZQP
    
    return X2P, Z2P, XQP, ZQP    #cost: 6M+4S+8a	
    
    
################################################################


#function for computing [2^e](X:Z) via repeated doublings
def xDBLe(XP,ZP,A,C,e):
	#input: projective coordinates xP=XP/ZP
	#       curve constant A/C
	#output: projective coordinates of x(2^e*P)=XeP/ZeP
	A24num = C + C                      #code from msr
	A24den = A24num + A24num
	A24num = A24num + A
	
	XeP = XP
	ZeP = ZP
	
	for i in range(0,e):
		XeP, ZeP = xDBL(XeP, ZeP, A24num, A24den)
		
	return XeP, ZeP	                           #cost:4eM+2eS+(4e+3)a
	

####################################################################

#edwards-montgomery step in basefield
def xDBLADD_basefield(XP,ZP,XQ,ZQ,xPQ,A24,C24):
	#input: projective coordinates xP=XP/ZP and xQ=XQ/ZQ, 
    #       affine difference x(P-Q)=xPQ and 
    #       curve constant A24=(A+2)/4.	
    #output: projective coordinates of x(2P)=X2P/Z2P
    #        and x(Q+P)=XQP/ZQP
    # function assumes A24=1, C24=2 fixed
	
	t0 = XP + ZP   #Montgomery-addition
	t1 = XP - ZP
	XP = XQ - ZQ
	ZP = XQ + ZQ
	t2 = (XP * t0)%p
	t3 = (ZP * t1)%p
	ZP = t2 - t3
	XP = t2 + t3
	ZP = (ZP**2)%p
	XQP = (XP**2)%p
	ZQP = (xPQ * ZP)%p

	t1=(t1**2)%p  #Y^2    #edwards doubling
	t0=(t0**2)%p  #Z^2
	t2=t0+t1      #+ 
	t2=(t2**2)%p  #y^4+z^4+2y^2z^2
	t0=(t0**2)%p  #z^4
	t1=(t1**2)%p  #y^4
	t2=t2-t1
	X2P=(t2-t0)%p #2y^2z^2
	Z2P=(t0-t1)%p 

	return X2P, Z2P, XQP, ZQP     #cost: 3M+7S+8a


####################################################################


#triple point in Edwards-coordinates
def xTPL(X, Z, AE, DE):
	#input: projective x-coordinates of xP=X/Z
	#       curve constant A/C
	#output: projective x-coordinates of x(3P)=X3/Z3
	
	Ye = X-Z     #transformation to Edwards
	Ze = Z+X
	
	Ye, Ze = edDBL(Ye, Ze, AE, DE) #Edwards doubling
	
	t0 = Ze + Ze   #Montgomery addition
	t1 = Ye + Ye
	XP = X - Z
	ZP = X + Z
	t0 = XP * t0
	t1 = ZP * t1
	ZP = t0 - t1
	XP = t0 + t1
	ZP = ZP**2
	X3 = XP**2
	Z3 = X * ZP
	X3 = X3 * Z     #cost:7S+8M

	
	
	return X3, Z3               
	

#################################################################	

#triple point e times -> [3^e](X:Z)
def xTPLe(X, Z, A, C, e):
	#input: projective x-coordinates (X:Z) of P
	#       curve constant A/C
	#output: projective x-coordinates of x([3^e]P)=Xep/ZeP
	
	XeP = X
	ZeP = Z
	
	C2=C+C  #Edwards coefficients
	AE=A+C2
	DE=A-C2
	
	for i in range (0, e):
		XeP, ZeP = xTPL(XeP, ZeP, AE, DE)
		
	return XeP, ZeP	           #cost:8eM+4eS+(8e+3)a


######################################################################

#montgomery-ladder
def LADDER(x, m, A24, C24, AliceorBob):
	#input: affine x-coordinate of a point on E: B*y^2=x^3+A*x^2+x, 
	#       scalar m, curve constant (A+2)/4
	#output: projective coordinates x(mP)=X0/Z0 and x((m+1)P)=X1/Z1
	# function assumes A24=1, C24=2 fixed
	#if A24 != 1:
	#	print('wrong A24-value')
	#if C24 != 2:
	#	print('wrong C24-value')
	
	binary = lambda n: n>0 and [n&1]+binary(n>>1) or []
	bits = binary(m)
	
	A24, C24 = 1, 2
	X0, Z0 = 1, 0      #initialization with infinity
	X1, Z1 = x, 1
	
	if AliceorBob == 'Alice':
		nbits = eAbits
	else:
		nbits = eBbits
		
	#for i in range(0, nbits - len(bits)):
	#	X0, Z0, X1, Z1 = xDBLADD_basefield(X0, Z0, X1, Z1, x, A24, C24)
	
	for i in range(len(bits)-1, -1, -1):	
		if bits[i] == 0:
			X0, Z0, X1, Z1 = xDBLADD_basefield(X0, Z0, X1, Z1, x, A24, C24)
		else:
			X1, Z1, X0, Z0 = xDBLADD_basefield(X1, Z1, X0, Z0, x, A24, C24)	
			
	return X0, Z0, X1, Z1		#cost:5nM+4nS+9na	
						 	
	
#########################################################################

#function for computing P+[m]Q
def secret_pt(x, y, m, AliceorBob):
	#input: point P=(x,y) in base field subgroup, Q=(-x,iy), scalar m
	#output: RX0, RX1, RZ in Fp with (RX0+iRX1)/RZ is x-coordinate of P+[m]Q
	
	A24, C24 = 1, 2
	X0, Z0, X1, Z1 = LADDER(-x, m, A24, C24, AliceorBob)
	
	RZ = (x * Z0)%p
	RX0 = (X0 * x)%p
	t4 = (X0 + RZ)%p
	RZ = (X0 - RZ)%p
	t0 = (t4**2)%p
	RX0 = Z0 - RX0
	t0 = (t0 * X1)%p
	RX0 = (RX0 * RZ)%p
	t2 = (y * Z1)%p
	t1 = (y * Z0)%p
	t2 = t2 + t2
	RX1 = (t2 * Z0)%p
	RX0 = (RX0 * Z1)%p
	RX0 = RX0 - t0
	t1 = (t1 * RX1)%p
	t0 = (RX1**2)%p
	t2 = (t2 * RX1)%p
	RX1 = (t1 * RX0)%p
	t3 = t1 + RX0
	RX1 = RX1 + RX1
	t1 = t1 - RX0
	t1 = (t1 * t3)%p
	RZ = (RZ**2)%p
	t2 = (t2 * t4)%p
	t2 = (t2 * RZ)%p
	RZ = (t0 * RZ)%p
	RX0 = t1 - t2
	RX0 = RX0 % p
	RX1 = RX1 % p
	return RX0, RX1, RZ        #cost: 15M+3S+9a
	
	
#####################################################################


#three-point-ladder by de feo et al. calculates P+[m]Q
def LADDER_3_pt(m, xP, xQ, xPQ, A, AliceorBob):
	#input: affine x-coordinates xP, xQ, xPQ
	#       curve constant A, scalar m
	#output: projectove x.coordinate x(P+[m]Q)=WX/WZ
	
	binary = lambda n: n>0 and [n&1]+binary(n>>1) or []
	bits = binary(m)

	A24 = A + Complex(2)
	A24 = A24 * inv4
	
	UX = Complex(1) 
	UZ = Complex(0)                    #initialization with infinity
	VX = xQ
	VZ = Complex(1)
	WX = xP
	WZ = Complex(1)
	
	if AliceorBob == 'Alice':
		nbits = eAbits
	else:
		nbits = eBbits
		
	#for i in range(0, nbits - len(bits)):
	#	WX, WZ = xADD(UX, UZ, WX, WZ, xP)
	#	UX, UZ, VX, VZ = xDBLADD(UX, UZ, VX, VZ, xQ, A24)
		
	for i in range(len(bits)-1, -1, -1):	
		if bits[i] == 0:
			WX, WZ = xADD(UX, UZ, WX, WZ, xP)
			UX, UZ, VX, VZ = xDBLADD(UX, UZ, VX, VZ, xQ, A24)
		else:
			UX, UZ = xADD(UX, UZ, VX, VZ, xQ)
			VX, VZ, WX, WZ = xDBLADD(VX, VZ, WX, WZ, xPQ, A24)	
			
	return WX, WZ		#cost:9nM+6nS+(14n+3)a
	

#####################################################################	
	
#calculate 4-isogenies
def get_4_isog(X4, Z4):
	#input: projective point of order four (X4:Z4)
	#output: 4-isog curve with projective coefficient A/C and
	#        5 coefficients for evaluating
	
	coeff0 = X4 + Z4
	coeff3 = X4**2
	coeff4 = Z4**2
	coeff0 = coeff0**2
	coeff1 = coeff3 + coeff4
	coeff2 = coeff3 - coeff4
	coeff3 = coeff3**2
	coeff4 = coeff4**2
	A = coeff3 + coeff3
	coeff0 = coeff0 - coeff1
	A = A - coeff4
	C = coeff4
	A = A + A
	
	return A, C, [coeff0, coeff1, coeff2, coeff3, coeff4]	  #cost:5S+7a


######################################################################


#evaluate 4-isogenies: given coefficients from get_4_isog, evaluate at point in domain
def eval_4_isog(coeff, X, Z):
	#input: coefficients from get_4_isog
	#       projective point P=(X:Z)
	#output: projective point phi(P)=(X:Z) (overwritten since they replace inputs)
	
	X = coeff[0] * X
	t0 = coeff[1] * Z
	X = X - t0
	Z = coeff[2] * Z
	t0 = X - Z
	Z = X * Z
	t0 = t0**2
	Z = Z + Z
	Z = Z + Z
	X = t0 + Z
	Z = t0 * Z
	Z = coeff[4] * Z
	t0 = t0 * coeff[4]
	t1 = X * coeff[3]
	t0 = t0 - t1
	X = X * t0
	
	return X, Z              #cost:9M+1S+6a


######################################################################

#first 4-isogenie is different
def first_4_isog(X4, Z4, A):
	#input: projective point (X4:Z4) and affine curve constant A (start parameter is affine)
	#output: projective point (X:Z) in the codomain
	#        isogenous curve constant A/C      (inputs overwritten)
	
	t0 = X4**2
	X = Z4**2
	Z = X4 * Z4
	X4 = A * Z
	Z = Z + Z
	Z4 = Z - X4
	t0 = t0 + X
	X = t0 + Z
	Z = t0 - Z
	X4 = X4 + t0
	X = X * X4
	Z = Z4 * Z
	C = Complex(A.re - 2,A.im)
	An = Complex(0)
	An.re = A.re + 6
	An.re = An.re + An.re
	An.im = A.im + A.im
	An = Complex(An.re , An.im)
	
	return X, Z, An, C      #cost: 4M+2S+9a
	
	
####################################################################	 

#compute 3-isogenies
def get_3_isog(X3, Z3):
	#input: projective point (X3:Z3) of order 3
	#ouput: coefficient A/C of 3-isog curve. no other coeff needed
	
	t0 = X3**2
	t1 = t0 + t0
	t0 = t0 + t1
	t1 = Z3**2
	A = t1**2
	t1 = t1 + t1
	C = t1 + t1
	t1 = t0 - t1
	t1 = t1 * t0
	A = A - t1
	A = A - t1
	A = A - t1
	t1 = X3 * Z3
	C = C * t1
	
	return A, C             #cost: 3M+3S+8a
	

####################################################################

#evaluate 3-isogenies
def eval_3_isog(X3, Z3, X, Z):
	#input: projective point (X3:Z3) of order 3
	#       projective x coordinate x(P)=X/Z
	#output: projective x-coordinate of phi(X:Z)
	t0 = X3 * X
	t1 = Z3 * X
	t2 = Z3 * Z
	t0 = t0 - t2
	t2 = Z * X3
	t1 = t1 - t2
	t0 = t0**2
	t1 = t1**2
	X = X * t0
	Z = Z * t1
	
	return X, Z              #cost: 6M+2S+2a
	

######################################################################


#with affine x-coordinate of P, return projective x-coordinates of Q-P where 
#Q=tau(P) is image of the distortion map

def distort_and_diff(xP):
	#input: affine x-coordinate xP
	#output: point (x(Q-P),z(Q-P)) with Q=tau(P)
	
	XD = (xP**2)%p
	XD = XD + 1
	XD = Complex(0, XD)
	ZD = (xP + xP)%p
	ZD = Complex(ZD)
	
	return XD, ZD
	
	
######################################################################

#compute inverses of 3 elements
def inv_3_way(z1, z2, z3):
	#input: 3 values z1, z2, z3
	#output: their inverses, inputs overwritten		
	
	t0 = z1 * z2
	t1 = t0 * z3
	t1 = inv(t1)
	t2 = z3 * t1
	t3 = t2 * z2
	z2 = t2 * z1
	z3 = t0 * t1
	z1 = t3
	
	return z1, z2, z3         #cost: 6M+1I


#######################################################################

#calculate A from x-coordinates of P, Q, R, such that R=Q-P is on the
#montgomery-curve E_A: y^2=x^3+A*x^2+x
def get_A(xP, xQ, xR):
	#input: x-coordinates xP, xQ, xR
	#output: coefficient A
	
	t1 = xP + xQ
	t0 = xP * xQ
	A = xR * t1
	A = A + t0
	t0 = t0 * xR
	A = A - Complex(1)
	t0 = t0 + t0
	t1 = t1 + xR
	t0 = t0 + t0
	A = A**2
	t0 = inv(t0)
	A = A * t0
	A = A - t1

	return A                 #cost: 4M+1S+7a+1I
##########################################################################

#caluclate the inverse of an element
def inv(z):
	re = z.re
	im = z.im
	den = re**2
	t0 = im**2
	den = den + t0
	den = int(den)
	den = pow(den, p-2, p)
	re = re * den
	im = im * den
	z = Complex(re, -im)
	
	return z


######################################################################

















#KEYGEN

def keygen_Alice(SK_Alice, params, splits, MAX):
	#input: secret random even number in (1,oA-1)
	#       public parameters [XPB, XPA, YPA]
	#output: public key [phi_A(x(PB)),phi_A(x(QB)),phi_A(x(QB-PB))] 
	
	A, C = Complex(0), Complex(1)  #starting montgomery curve
	phiPX = params[0]  #Bob's starting points -> public key
	phiPZ = Complex(1)
	phiQX = Complex(-phiPX)
	phiQZ = Complex(1)
	
	phiDX, phiDZ = distort_and_diff(phiPX)   #(phiDX:phiDZ)=x(Q-P)
	phiPX = Complex(phiPX)
	
	#compute the point x(R)=(RX:RZ) via secre_pt, R=P+[SK_Alice]Q
	RX0, RX1, RZ = secret_pt(params[1], params[2], SK_Alice, 'Alice')
	RX = Complex(RX0, RX1)
	RZ = Complex(RZ)
	
	#counters
	iso, mul = 0, 0
	
	#first 4-isogeny (different from rest)
	phiPX, phiPZ, A2, C2 = first_4_isog(phiPX, phiPZ, A)
	phiQX, phiQZ, A2, C2 = first_4_isog(phiQX, phiQZ, A)
	phiDX, phiDZ, A2, C2 = first_4_isog(phiDX, phiDZ, A)
	RX, RZ, A, C = first_4_isog(RX, RZ, A)
	iso = iso + 4
	
	pts = []
	index = 0
	
	#Alice's main loop
	for row in range(1, MAX):
		
		#multiply (RX:RZ) until it has order 4. store intermediate pts
		while index < (MAX - row):
			pts.append([RX, RZ, index])
			m = splits[MAX-index-row]
			RX, RZ = edDBLe(RX, RZ, A, C, 2*m)
			mul = mul + m
			index = index + m	
			
		#compute isogeny	
		A, C, consts = get_4_isog(RX, RZ)
		
		#evaluate 4-isogeny at every point in pts
		for i in range(0, len(pts)):
			pts[i][0], pts[i][1] = eval_4_isog(consts, pts[i][0], pts[i][1])
			iso = iso + 1
			
		#evaluate 4-isogeny at Bob's points		
		phiPX, phiPZ = eval_4_isog(consts, phiPX, phiPZ) #P=phi(P)
		phiQX, phiQZ = eval_4_isog(consts, phiQX, phiQZ) #Q=phi(Q)
		phiDX, phiDZ = eval_4_isog(consts, phiDX, phiDZ) #D=phi(D)
		iso = iso + 3
		
		#R becomes last entry of pts, last entry is removed from pts
		RX = pts[len(pts)-1][0]
		RZ = pts[len(pts)-1][1]
		index = pts[len(pts)-1][2]
		del pts[-1]
	
	#compute last isogeny
	A, C, consts = get_4_isog(RX, RZ)
	phiPX, phiPZ = eval_4_isog(consts, phiPX, phiPZ) #P=phi(P)
	phiQX, phiQZ = eval_4_isog(consts, phiQX, phiQZ) #Q=phi(Q)
	phiDX, phiDZ = eval_4_isog(consts, phiDX, phiDZ) #D=phi(D)
	iso = iso + 3
			
	#compute affine x-coordinates
	phiPZ, phiQZ, phiDZ = inv_3_way(phiPZ, phiQZ, phiDZ)
	phiPX = phiPX * phiPZ
	phiQX = phiQX * phiQZ
	phiDX = phiDX * phiDZ
	
	#Alices's public key, values in Fp2
	PK_Alice = [phiPX, phiQX, phiDX]
	
	msg="Alice's keygen needs "+str(mul)+" multiplications by 4 and "+str(iso)+" isogenies"
	print(msg)
	print('')
	keysize = len(binary(phiPX.re)) + len(binary(phiPX.im)) + len(binary(phiQX.re)) + len(binary(phiQX.im))+ len(binary(phiDX.re)) + len(binary(phiDX.im))
	msg="Keysize of Alice's public key: " + str(keysize) + " bits"
	print(msg)

	return PK_Alice


#########################################################################

def keygen_Bob(SK_Bob, params, splits, MAX):
	#input: secret random number in (1,oB-1)
	#       public parameters [XPA, XPB, YPB]
	#output: public key [phi_B(x(PA)),phi_B(x(QA)),phi_B(x(QA-PA))]
	
	A, C = Complex(0), Complex(1)  #starting montgomery curve
	phiPX = params[0]   #Bob's starting points -> public key
	phiPZ = Complex(1)
	phiQX = Complex(-phiPX)
	phiQZ = Complex(1)
	
	phiDX, phiDZ = distort_and_diff(phiPX)   #(phiDX:phiDZ)=x(Q-P) 
	phiPX = Complex(phiPX)
	
	#compute the point x(R)=(RX:RZ) via secret_pt, R=P+[SK_Alice]Q
	RX0, RX1, RZ = secret_pt(params[1], params[2], SK_Bob, 'Bob')
	RX = Complex(RX0, RX1)
	RZ = Complex(RZ)
	
	#counters
	iso, mul = 0, 0
	
	pts = []
	index = 0
	
	#Bob's main loop
	for row in range(1, MAX):
		
		#multiply (RX:RZ) until it has order 3. store intermediate pts
		while index < (MAX - row):
			pts.append([RX, RZ, index])
			m = splits[MAX-index-row]
			RX, RZ = xTPLe(RX, RZ, A, C, m)
			mul = mul + m
			index = index + m
		
		#compute isogeny	
		A, C = get_3_isog(RX, RZ)
		
		#evaluate 3-isogeny at every point in pts
		for i in range(0, len(pts)):
			pts[i][0], pts[i][1] = eval_3_isog(RX, RZ, pts[i][0], pts[i][1])
			iso = iso + 1
			
		#evaluate 3-isogeny at Alice's points		
		phiPX, phiPZ = eval_3_isog(RX, RZ, phiPX, phiPZ) #P=phi(P)
		phiQX, phiQZ = eval_3_isog(RX, RZ, phiQX, phiQZ) #Q=phi(Q)
		phiDX, phiDZ = eval_3_isog(RX, RZ, phiDX, phiDZ) #D=phi(D)
		iso = iso + 3
		
		#R becomes last entry of pts, last entry is removed from pts
		RX = pts[len(pts)-1][0]
		RZ = pts[len(pts)-1][1]
		index = pts[len(pts)-1][2]
		del pts[-1]
	
	#compute last isogeny
	A, C = get_3_isog(RX, RZ)
	phiPX, phiPZ = eval_3_isog(RX, RZ, phiPX, phiPZ) #P=phi(P)
	phiQX, phiQZ = eval_3_isog(RX, RZ, phiQX, phiQZ) #Q=phi(Q)
	phiDX, phiDZ = eval_3_isog(RX, RZ, phiDX, phiDZ) #D=phi(D)
	iso = iso + 3
	
	#compute affine x-coordinates
	phiPZ, phiQZ, phiDZ = inv_3_way(phiPZ, phiQZ, phiDZ)
	phiPX = phiPX * phiPZ
	phiQX = phiQX * phiQZ
	phiDX = phiDX * phiDZ	
	
	#Bob's public key, values in Fp2
	PK_Bob = [phiPX, phiQX, phiDX]
	
	msg="Bob's keygen needs "+str(mul)+" multiplications by 3 and "+str(iso)+" isogenies"
	print(msg)
	print('')
	keysize = len(binary(phiPX.re)) + len(binary(phiPX.im)) + len(binary(phiQX.re)) + len(binary(phiQX.im))+ len(binary(phiDX.re)) + len(binary(phiDX.im))
	msg="Keysize of Bob's public key: " + str(keysize) + " bits"
	print(msg)
	
	return PK_Bob
	

######################################################################


def shared_secret_Alice(SK_Alice, PK_Bob, splits, MAX):
	#input: Alices's secret key SK_Alice
	#       Bob's public key
	#output: Alice's shared secret: j-invariant of E_AB
	
	A = get_A(PK_Bob[0], PK_Bob[1], PK_Bob[2])
	C = Complex(1)     #start on Bob's curve
	
	#compute R=phi_B(xPA)+SK_Alice*phi_B(xQA)
	RX, RZ = LADDER_3_pt(SK_Alice, PK_Bob[0], PK_Bob[1], PK_Bob[2], A, 'Alice')
	iso, mul = 0, 0  #counters
	
	#first isogeny
	RX, RZ, A, C = first_4_isog(RX, RZ, A)
	iso = iso + 1
	
	pts = []
	index = 0
	
	#main loop
	for row in range(1, MAX):
		
		#multiply (RX:RZ) until it has order 4. store intermediate pts
		while index < (MAX - row):
			pts.append([RX, RZ, index])
			m = splits[MAX-index-row]
			RX, RZ = edDBLe(RX, RZ, A, C, 2*m)
			mul = mul + m
			index = index + m
		
		#compute isogeny	
		A, C, consts = get_4_isog(RX, RZ)
		
		#evaluate 4-isogeny at every point in pts
		for i in range(0, len(pts)):
			pts[i][0], pts[i][1] = eval_4_isog(consts, pts[i][0], pts[i][1])
			iso = iso + 1
		
		#R becomes last entry of pts, last entry is removed from pts
		RX = pts[len(pts)-1][0]
		RZ = pts[len(pts)-1][1]
		index = pts[len(pts)-1][2]
		del pts[-1]
	
	#compute last isogeny
	A, C, consts = get_4_isog(RX, RZ)
		
	secret_Alice = j_inv(A, C)	
	
	msg="Alice's secret needs "+str(mul)+" multiplications by 4 and "+str(iso)+" isogenies"
	print(msg)
	
	return secret_Alice



######################################################################



def shared_secret_Bob(SK_Bob, PK_Alice, splits, MAX):
	#input: Bob's secret key SK_Alice
	#       Alices's public key
	#output: Bob's shared secret: j-invariant of E_BA
	
	A = get_A(PK_Alice[0], PK_Alice[1], PK_Alice[2])
	C = Complex(1)     #start on Alice's curve
	
	#compute R=phi_A(xPB)+SK_Bob*phi_A(xQB)
	RX, RZ = LADDER_3_pt(SK_Bob, PK_Alice[0], PK_Alice[1], PK_Alice[2], A, 'Bob')
	iso, mul = 0, 0  #counters
	
	pts = []
	index = 0
	
	#Bob's main loop
	for row in range(1, MAX):
		
		#multiply (RX:RZ) until it has order 3. store intermediate pts
		while index < (MAX - row):
			pts.append([RX, RZ, index])
			m = splits[MAX-index-row]
			RX, RZ = xTPLe(RX, RZ, A, C, m)
			mul = mul + m
			index = index + m
		
		#compute isogeny	
		A, C = get_3_isog(RX, RZ)
		
		#evaluate 3-isogeny at every point in pts
		for i in range(0, len(pts)):
			pts[i][0], pts[i][1] = eval_3_isog(RX, RZ, pts[i][0], pts[i][1])
			iso = iso + 1
			
		#R becomes last entry of pts, last entry is removed from pts
		RX = pts[len(pts)-1][0]
		RZ = pts[len(pts)-1][1]
		index = pts[len(pts)-1][2]
		del pts[-1]
	
	#compute last isogeny
	A, C = get_3_isog(RX, RZ)
	
	secret_Bob = j_inv(A, C)	
	
	msg="Bob's secret needs "+str(mul)+" multiplications by 3 and "+str(iso)+" isogenies"
	print(msg)
	
	return secret_Bob	


#parameters defining prime p=lA^eA*lB^e_B*f-1
lA=2
lB=3
eA=372
eB=239
#eA=15
#eB=8
f=1

binary = lambda n: n>0 and [n&1]+binary(n>>1) or []

eAbits = len(binary(lA**eA))
eBbits = len(binary(lB**eB))

#defining p (must be prime!)
p=(lA**eA)*(lB**eB)*f-1   

#inverse of 4, needed for 3-pt-ladder
inv4 = inv(Complex(4))
	
#values for eA=372, eB=239
XPA = 5784307033157574162391672474522522983832304511218905707704962058799572462719474192769980361922537187309960524475241186527300549088533941865412874661143122262830946833377212881592965099601886901183961091839303261748866970694633
YPA = 5528941793184617364511452300962695084942165460078897881580666552736555418273496645894674314774001072353816966764689493098122556662755842001969781687909521301233517912821073526079191975713749455487083964491867894271185073160661
XPB = 4359917396849101231053336763700300892915096700013704210194781457801412731643988367389870886884336453245156775454336249199185654250159051929975600857047173121187832546031604804277991148436536445770452624367894371450077315674371
YPB = 106866937607440797536385002617766720826944674650271400721039514250889186719923133049487966730514682296643039694531052672873754128006844434636819566554364257913332237123293860767683395958817983684370065598726191088239028762772

#values for eA=8, eB=5
#XPA = 4437
#YPA = 55467
#XPB = 24048
#YPB = 57850

#values for eA=13, eB=7
#XPA = 4698102
#YPA = 1371375
#XPB = 1258275
#YPB = 10923545

#values for eA=15, eB=8
#XPA = 144036251
#YPA = 40988612
#XPB = 4982149
#YPB = 74338728

params_Alice = [XPB, XPA, YPA]
params_Bob = [XPA, XPB, YPB]



#################################################################
#strategy paramters from MSR
splits_Alice = [0, 1, 1, 2, 2, 2, 3, 4, 4, 4, 4, 5, 5, 6, 7, 8, 8, 9, 9, 9, 9, 9, 9, 9, 12, 11,\
12, 12, 13, 14, 15, 16, 16, 16, 16, 16, 16, 17, 17, 18, 18, 17, 21, 17, 18, 21,\
20, 21, 21, 21, 21, 21, 22, 25, 25, 25, 26, 27, 28, 28, 29, 30, 31, 32, 32, 32,\
32, 32, 32, 32, 33, 33, 33, 35, 36, 36, 33, 36, 35, 36, 36, 35, 36, 36, 37, 38,\
38, 39, 40, 41, 42, 38, 39, 40, 41, 42, 40, 46, 42, 43, 46, 46, 46, 46, 48, 48,\
48, 48, 49, 49, 48, 53, 54, 51, 52, 53, 54, 55, 56, 57, 58, 59, 59, 60, 62, 62,\
63, 64, 64, 64, 64, 64, 64, 64, 64, 65, 65, 65, 65, 65, 66, 67, 65, 66, 67, 66,\
69, 70, 66, 67, 66, 69, 70, 69, 70, 70, 71, 72, 71, 72, 72, 74, 74, 75, 72, 72,\
74, 74, 75, 72, 72, 74, 75, 75, 72, 72, 74, 75, 75, 77, 77, 79, 80, 80, 82 ]

splits_Bob = [0, 1, 1, 2, 2, 2, 3, 3, 4, 4, 4, 5, 5, 5, 6, 7, 8, 8, 8, 8, 9, 9, 9, 9, 9, 10,\
12, 12, 12, 12, 12, 12, 13, 14, 14, 15, 16, 16, 16, 16, 16, 17, 16, 16, 17, 19,\
19, 20, 21, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 24, 24, 25, 27, 27, 28, 28,\
29, 28, 29, 28, 28, 28, 30, 28, 28, 28, 29, 30, 33, 33, 33, 33, 34, 35, 37, 37,\
37, 37, 38, 38, 37, 38, 38, 38, 38, 38, 39, 43, 38, 38, 38, 38, 43, 40, 41, 42,\
43, 48, 45, 46, 47, 47, 48, 49, 49, 49, 50, 51, 50, 49, 49, 49, 49, 51, 49, 53,\
50, 51, 50, 51, 51, 51, 52, 55, 55, 55, 56, 56, 56, 56, 56, 58, 58, 61, 61, 61,\
63, 63, 63, 64, 65, 65, 65, 65, 66, 66, 65, 65, 66, 66, 66, 66, 66, 66, 66, 71,\
66, 73, 66, 66, 71, 66, 73, 66, 66, 71, 66, 73, 68, 68, 71, 71, 73, 73, 73, 75,\
75, 78, 78, 78, 80, 80, 80, 81, 81, 82, 83, 84, 85, 86, 86, 86, 86, 86, 87, 86,\
88, 86, 86, 86, 86, 88, 86, 88, 86, 86, 86, 88, 88, 86, 86, 86, 93, 90, 90, 92,\
92, 92, 93, 93, 93, 93, 93, 97, 97, 97, 97, 97, 97 ]

MAX_Alice = 185
MAX_Bob = 239





#######################################################################




n_Alice = randint(0,(lA**eA)/2)
n_Alice = 2*n_Alice
print("Alice's secret key:")
print(n_Alice)
print('')
n_Bob= randint(0,lB**eB)
print("Bob's secret key:")
print(n_Bob)
print('')

PKA = keygen_Alice(n_Alice, params_Alice, splits_Alice, MAX_Alice)
print('')
print("Alice's Public Key:")
print(PKA[0])
print(PKA[1])
print(PKA[2])
print('')

PKB = keygen_Bob(n_Bob, params_Bob, splits_Bob, MAX_Bob)
print('')
print("Bob's Public Key:")
print(PKB[0])
print(PKB[1])
print(PKB[2])
print('')

SKA = shared_secret_Alice(n_Alice, PKB, splits_Alice, MAX_Alice)
print('')
print("Alice's shared secret:")
print(SKA)
print('')

SKB = shared_secret_Bob(n_Bob, PKA, splits_Bob, MAX_Bob)
print('')
print("Bob's shared secret:")
print(SKB)
print('')

if SKA==SKB:
	print('keys are equal :)')
else:
	print('something went wrong :(')
	if n_Alice % 2 != 0:
		print("Error: Alice's secret key must be even!")

print('')
print('')
print('performance stats:')
print('')

pr.disable()
s = StringIO.StringIO()
sortby = 'cumulative'
ps = pstats.Stats(pr, stream=s).sort_stats(sortby)
ps.print_stats()
print s.getvalue()


