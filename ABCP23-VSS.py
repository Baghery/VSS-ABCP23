from hashlib import sha256,sha1
from time import time

#############################
### ====  ABCP23 VSS  ==== ##
#############################

# global parameters
N = 2^255-19   # Curve 25519
ZN = Integers(N)
LAM = Integers(2^128)
R.<x> = PolynomialRing(ZN)

# routines
def shamir_ABCP(n):
    t = n//2 - 1        # assumes n is even!
    f = R.random_element(degree=t)
    feval = [f(x=i) for i in range(1,n+1)]
    return f,feval

def prover_ABCP(f,feval):
    t = f.degree()
    n = len(feval)
    b = R.random_element(degree=t)
    y = [ [LAM.random_element(),LAM.random_element()] for i in range(n)]
    C,C_ = "",""

    for i in range(1,n+1): # parties are 0..n-1
        bi = b(x=i)
        C += sha256((str(bi)+str(y[i-1][0])).encode()).hexdigest()+str(",")
        C_+= sha256((str(feval[i-1])+str(y[i-1][1])).encode()).hexdigest()+str(",")
    C = C[:-1]
    C_= C_[:-1]
    d = Integer(ZN(int(sha256(str(C+C_).encode()).hexdigest(),16)))
    r = b-d*f
    return C,C_,r,y

def verifier_ABCP(i,C,C_,r,yi,yi_,xi):
    ri = r(x=i)
    d = Integer(ZN(int(sha256(str(C+C_).encode()).hexdigest(),16)))
    Ci  = sha256((str(ri+d*xi)+str(yi)).encode()).hexdigest()
    Ci_ = sha256((str(xi)+str(yi_)).encode()).hexdigest()
    return Ci == C.split(',')[i-1] and Ci_ == C_.split(',')[i-1]

# benchmark function
def benchmark_ABCP23(n):
    N = 2^255-19       # Curve 25519
    ZN = Integers(N)
    LAM = Integers(2^128)
    R.<x> = PolynomialRing(ZN)

    Ts = time()
    f,feval = shamir_ABCP(n)
    Ts = time() - Ts

    Tp = time()
    C,C_,r,y = prover_ABCP(f,feval)
    Tp = time() - Tp

    i = randint(1,n-1) # pick a random verifier

    Tv = time()
    b = verifier_ABCP(i,C,C_,r,y[i-1][0],y[i-1][1],feval[i-1])
    Tv = time() - Tv

    if b == False: print(b)
    return Ts,Tp,Tv


#############################
### ==== Pedersen VSS ==== ##
#############################

# global parameters

p = 2^255-19         # Curve 25519
q = 2^252 + 27742317777372353535851937790883648493 #point group size
Zq = Integers(q)     # group of multiplication map
Am = 486662          # Montgomery A-coefficient
Ar = int((Am+2)/4)   # reduced Montgomery coefficent
E = EllipticCurve(GF(p),[0,Am,0,1,0])
RP.<x> = PolynomialRing(Zq)

G = E.random_point() # generator 1
while G.order() != q:
    G = E.random_point()
s = Zq.random_element()
H = Integer(s)*G     # generator 2


# Montgomery subroutines

def xADD(P,Q,R): # points are of the form [X,Z]
    [XP,ZP] = [P[0],P[1]];
    [XQ,ZQ] = [Q[0],Q[1]];
    [XR,ZR] = [R[0],R[1]];

    V0 = XP + ZP
    V1 = XQ - ZQ
    V1 = V1 * V0
    V0 = XP - ZP
    V2 = XQ + ZQ
    V2 = V2 * V0
    V3 = V1 + V2
    V3 = V3^2
    V4 = V1 - V2
    V4 = V4^2
    Xp = ZR * V3
    Zp = XR * V4
    
    return [Xp,Zp]

def xDBL(P): # points are of the form [X,Z]
    [XP,ZP] = [P[0],P[1]]
    
    V1 = XP + ZP
    V1 = V1^2
    V2 = XP - ZP
    V2 = V2^2
    X2 = V1 * V2
    V1 = V1 - V2
    V3 = Ar * V1
    V3 = V3 + V2
    Z2 = V1 * V3
    
    return [X2,Z2]

def Montgomery_ladder(k,P): # points are of the form [X,Z]
    x0,x1 = P,xDBL(P)
    k = k.binary()
    l = len(k)
    for i in range(1,l):
        if k[i]=='0':
            x0,x1 = xDBL(x0),xADD(x0,x1,P)
        if k[i]=='1':
            x0,x1 = xADD(x0,x1,P),xDBL(x1)
    return x0,x1

def recover_y(P,Q,R):
    [XP,YP] = [P[0],P[1]] # P is an actual elliptic curve point in the form (X:Y:Z)
    [XQ,ZQ] = [Q[0],Q[1]]
    [XR,ZR] = [R[0],R[1]]
        
    V1 = XP * ZQ
    V2 = XQ + V1
    V3 = XQ - V1
    V3 = V3^2
    V3 = V3 * XR
    V1 = 2*Am*ZQ
    
    V2 = V2 + V1
    V4 = XP * XQ
    V4 = V4 + ZQ
    V2 = V2 * V4
    V1 = V1 * ZQ
    V2 = V2 - V1
    V2 = V2 * ZR
    
    Y  = V2 - V3
    V1 =  2 * YP
    V1 = V1 * ZQ
    V1 = V1 * ZR
    X  = V1 * XQ
    Z  = V1 * ZQ
    
    return E(X,Y,Z)

def fast_multiply(k,P): # use montgomery ladder and y-recovery
    PM = [P[0],P[2]] # X-Z coordinates
    x0,x1 = Montgomery_ladder(Integer(k),PM)
    return E(recover_y(P,x0,x1))


# routines
def shamir_P(n):
    t = n//2-1 # assumes n is even!
    f = RP.random_element(degree=t)
    feval = [f(x=i) for i in range(1,n+1)]
    return f,feval

def prover_P(f,feval):
    t = f.degree()
    C = [0 for _ in range(t+1)]
    g = RP.random_element(degree=t)
    fcoeff = f.coefficients(sparse=False)
    gcoeff = g.coefficients(sparse=False)
    geval = [g(x=i) for i in range(1,n+1)]
    for i in range(t+1):
        C[i] = fast_multiply(Integer(fcoeff[i]),G) + fast_multiply(Integer(gcoeff[i]),H)
    return g,C

def verifier_P(a,b,C,i):
    S = C[0]
    for j in range(1,len(C)):
        S += fast_multiply(Integer(Zq(i)^j),C[j])
    return S == fast_multiply(a,G) + fast_multiply(b,H)


# benchmark function
def benchmark_Pedersen(n):
    Ts = time()
    f,feval = shamir_P(n)
    Ts = time() - Ts

    Tp = time()
    g,C = prover_P(f,feval)
    Tp = time()-Tp

    i = randint(1,n) # sample verifier
    a,b = Integer(f(x=i)),Integer(g(x=i))

    Tv = time()
    boo = verifier_P(a,b,C,i)
    Tv = time()-Tv

    if boo == False: print(boo)
    return Ts,Tp,Tv


# running the benchmark for different numbers of parties n
# N=[16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384]
N=[16, 32, 128, 512, 2048, 8192]

for i in range(len(N)):
  n = N[i]  
  iteration = 5
  if n < 513: iteration = 100

  print("==================================================================================")
  print("Benchmarking Shamir and VSS Schemes Pedersen and ABCP23 for (n, t) =", (n, n/2-1))
  print("==================================================================================")

  Ts1f = 0 
  Tp1f = 0
  Tv1f = 0
  
  Ts2f = 0 
  Tp2f = 0
  Tv2f = 0
  
  for i in range(iteration):
    Ts1,Tp1,Tv1 = benchmark_Pedersen(n)
    Ts2,Tp2,Tv2 = benchmark_ABCP23(n)

    Ts1f += Ts1 
    Tp1f += Tp1
    Tv1f += Tv1
    
    Ts2f += Ts2 
    Tp2f += Tp2
    Tv2f += Tv2
    
  print("    ======================== Shamir Secret Sharing ===========================")
  print("    Shamir    -- sharing time:       ",(Ts2f)/iteration)
  print("    ================= Verifiable Secret Sharing Schemes ======================")
  print("    Pedersen  -- sharing time:       ",(Ts1f+Tp1f)/iteration)
  print("    ABCP23    -- sharing time:       ",(Ts2f+Tp2f)/iteration)

  print("    ========================= Verification ===================================")
  print("    Pedersen  -- verification time:  ",Tv1f/iteration)
  print("    ABCP23    -- verification time:  ",Tv2f/iteration)
  print("    ==========================================================================")