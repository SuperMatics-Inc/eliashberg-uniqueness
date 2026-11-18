"""Independent Aase replay: SciPy trust-region solve, mpmath.iv, exact integers.
No imports from the original implementation. Interval matrix preconditioning uses
fixed-point integer endpoint enclosures, with fmpz_mat for EXACT multiplication;
Arb and arb_mat are never used. All scientific values are calculated, not measured.
Run: python scripts/rigor_independent.py --out logs/rigor/independent.json
"""
import argparse
import json
import os
from pathlib import Path
import time
for key in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[key] = '1'
import numpy as np
from scipy.optimize import least_squares
from mpmath import mp, iv
from flint import fmpz_mat

M = 175
SIZE = 3 * M
mp.dps = 65
iv.dps = 60
SCALE = 1 << 160
RATIOS = ((('4','5'),('1','10000'),('3','1000')),
          (('1','10000'),('7','5'),('3','1000')),
          (('3','1000'),('3','1000'),('1','200')))

def endpoints(x):
    return mp.make_mpf(x._mpi_[0]), mp.make_mpf(x._mpi_[1])

def bounds_int(x):
    lo, hi = endpoints(x)
    return int(mp.floor(lo * SCALE)), int(mp.ceil(hi * SCALE))

def text(x):
    return [mp.nstr(v, 55) for v in endpoints(x)]

def independent_coefficients(frozen):
    k = np.arange(2*M + 1)
    rat = np.array([[int(p)/int(q) for p,q in row] for row in RATIOS])
    l0 = (85*rat)**2 / 2000
    kernel = l0[:,:,None] * 100 / (100 + np.pi**2*k**2)
    a, n = np.divmod(np.arange(SIZE), M)
    A = kernel[a[:,None],a[None,:],abs(n[:,None]-n[None,:])]
    B = kernel[a[:,None],a[None,:],n[:,None]+n[None,:]+1]
    D, W = A-B, A+B
    np.fill_diagonal(D,0)
    np.fill_diagonal(W,2*np.diag(B))
    w = (2*n+1).astype(float)
    if frozen:
        for i in range(SIZE):
            w[i] += kernel[a[i],:,M-n[i]:M+n[i]+1].sum()
    return w,D,W

def residual(x,w,D,W):
    s,c = np.sin(x),np.cos(x)
    return w*s+s*(D@c)-c*(W@s)

def jacobian(x,w,D,W):
    s,c = np.sin(x),np.cos(x)
    H = -D*np.outer(s,s)-W*np.outer(c,c)
    np.fill_diagonal(H,w*c+c*(D@c)+s*(W@s)-np.diag(W)*c*c)
    return H

def solve(frozen, signed):
    w,D,W = independent_coefficients(frozen)
    n = np.arange(M)
    # Direct angle initialization, unrelated to the original gap fixed-point solver.
    x = np.arctan(np.array([5.,13.,0.0001])[:,None]/(2*n+1)).ravel()
    if signed:
        x[M:] *= -1
    fit = least_squares(residual,x,jac=jacobian,args=(w,D,W),
                        method='trf',ftol=1e-14,xtol=1e-14,gtol=1e-13,max_nfev=100)
    x = fit.x
    for _ in range(4):
        x -= np.linalg.solve(jacobian(x,w,D,W),residual(x,w,D,W))
    assert np.max(abs(residual(x,w,D,W))) < 1e-10
    assert np.all(x[:M]>0)
    assert np.all(x[M:]<0) if signed else np.all(x>0)
    return x,np.linalg.inv(jacobian(x,w,D,W)),float(np.max(abs(residual(x,w,D,W))))

def kernel_iv():
    vp = 100/(iv.pi**2)
    return [[[((iv.mpf(85)*iv.mpf(p)/iv.mpf(q))**2/2000)*vp/(vp+k*k)
              for k in range(2*M+1)] for p,q in row] for row in RATIOS]

def certify(frozen,signed,ker,mutant=None):
    start=time.time()
    x,C,res=solve(frozen,signed)
    if mutant == 'shifted-center':
        x[0] += 0.01
    r=mp.mpf('1e-13')
    ri=iv.mpf(str(r))
    xx=[iv.mpf(float(v)) for v in x]
    ss,cc=[iv.sin(v) for v in xx],[iv.cos(v) for v in xx]
    w=[];D=[];W=[]
    for i in range(SIZE):
        a,n=divmod(i,M)
        wi=iv.mpf(2*n+1)
        if frozen:
            wi += sum((ker[a][b][t] for b in range(3) for t in range(M-n,M+n+1)),iv.mpf(0))
        w.append(wi)
        dr=[];wr=[]
        for j in range(SIZE):
            b,m=divmod(j,M)
            aa,bb=ker[a][b][abs(n-m)],ker[a][b][n+m+1]
            dr.append(iv.mpf(0) if i==j else aa-bb)
            wr.append(2*bb if i==j else aa+bb)
        D.append(dr);W.append(wr)
    dc=[];ws=[];rowsD=[];rowsW=[]
    for i in range(SIZE):
        dc.append(sum((D[i][j]*cc[j] for j in range(SIZE)),iv.mpf(0)))
        ws.append(sum((W[i][j]*ss[j] for j in range(SIZE)),iv.mpf(0)))
        rowsD.append(sum(D[i],iv.mpf(0)))
        rowsW.append(sum(W[i],iv.mpf(0)))
    grad=[w[i]*ss[i]+ss[i]*dc[i]-cc[i]*ws[i] for i in range(SIZE)]
    # Krawczyk matrices: midpoint/radius integer enclosures with scale 2^160.
    hm=[];hr=[];hrows=[]
    for i in range(SIZE):
        mid=[];rad=[];row_bound=0
        for j in range(SIZE):
            h=-D[i][j]*ss[i]*ss[j]-W[i][j]*cc[i]*cc[j]
            delta=2*ri*(D[i][j]+W[i][j])
            if i==j:
                h=w[i]*cc[i]+cc[i]*dc[i]+ss[i]*ws[i]-W[i][i]*cc[i]**2
                delta=ri*(w[i]+2*rowsD[i]+2*rowsW[i]+2*W[i][i])
            dl,du=endpoints(delta)
            h += iv.mpf([-du,du])
            lo,hi=bounds_int(h)
            m=(lo+hi)//2
            mid.append(m);rad.append(max(m-lo,hi-m))
            row_bound += max(abs(lo),abs(hi))
        hm.append(mid);hr.append(rad);hrows.append(row_bound)
    # Every double in C is converted EXACTLY to a scaled integer.
    ci=[]
    for row in C:
        rr=[]
        for v in row:
            numerator,denominator=float(v).as_integer_ratio()
            assert SCALE%denominator==0
            rr.append(numerator*(SCALE//denominator))
        ci.append(rr)
    cm=fmpz_mat(ci)
    product=cm*fmpz_mat(hm)
    error=fmpz_mat([[abs(v) for v in row] for row in ci])*fmpz_mat(hr)
    glo=[];ghi=[]
    for g in grad:
        lo,hi=bounds_int(g);glo.append(lo);ghi.append(hi)
    scale2=SCALE*SCALE
    contraction=mp.mpf(0); maxstep=mp.mpf(0); accepted=True
    # These comparisons are rational/integer, with no floating rounding in acceptance.
    rnum,rden=1,10**13
    for i in range(SIZE):
        row_error=sum(abs((scale2 if i==j else 0)-int(product[i,j]))+int(error[i,j]) for j in range(SIZE))
        yl=0;yu=0
        for j in range(SIZE):
            p=ci[i][j]
            yl+=p*(glo[j] if p>=0 else ghi[j])
            yu+=p*(ghi[j] if p>=0 else glo[j])
        y=max(abs(yl),abs(yu))
        accepted &= y*rden + rnum*row_error < rnum*scale2
        contraction=max(contraction,mp.mpf(row_error)/scale2)
        maxstep=max(maxstep,mp.mpf(y)/scale2)
    if mutant:
        assert not accepted,'mutant unexpectedly accepted'
        return {'mutant':mutant,'rejected':not accepted,'seconds':time.time()-start}
    assert accepted,'Krawczyk inclusion failed'
    assert all(iv.mpf(abs(float(v)))>ri and iv.mpf(abs(float(v)))+ri<iv.pi/2 for v in x)
    # Energy at root via a second-order Taylor bound, not original first-order method.
    K=sum((w[i]*(1-cc[i]) for i in range(SIZE)),iv.mpf(0))
    K+=sum((rowsD[i]-cc[i]*dc[i]-ss[i]*ws[i] for i in range(SIZE)),iv.mpf(0))/2
    # max ||H(X)||_infinity encloses each row. Taylor remainder <= r²/2 sum rows.
    gmax=sum((max(abs(lo),abs(hi)) for lo,hi in zip(glo,ghi)),0)
    slack=ri*(iv.mpf(gmax)/SCALE)+ri**2*(iv.mpf(sum(hrows))/SCALE)/2
    _,upper_slack=endpoints(2*slack)
    energy=2*K+iv.mpf([-upper_slack,upper_slack])
    record={'boundary':'frozen' if frozen else 'hard','branch':'pi' if signed else 's++',
            'solver':'scipy.optimize.least_squares(method=trf) + Newton',
            'float_residual':res,'radius':str(r),'krawczyk':True,
            'contraction_upper':mp.nstr(contraction,20),'newton_step_upper':mp.nstr(maxstep,20),
            'energy':text(energy),'seconds':time.time()-start}
    print(json.dumps(record),flush=True)
    return record,energy

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out',type=Path,default=Path('logs/rigor/independent.json'))
    p.add_argument('--mutant',action='store_true')
    args=p.parse_args()
    ker=kernel_iv();records=[];gaps={}
    energy_claims = {
        (False, False): ('-75.236285293566757956', '3.14e-19'),
        (False, True): ('-75.236281622169900901', '3.47e-19'),
        (True, False): ('-75.120037066569992192', '2.95e-19'),
        (True, True): ('-75.120033399520462553', '6.83e-19'),
    }
    for frozen in (False,True):
        pp,epp=certify(frozen,False,ker);pi,epi=certify(frozen,True,ker)
        for signed, energy in ((False,epp),(True,epi)):
            center_text,radius_text=energy_claims[frozen,signed]
            claim=iv.mpf(center_text)+iv.mpf([-mp.mpf(radius_text),mp.mpf(radius_text)])
            elo,ehi=endpoints(energy);clo,chi=endpoints(claim)
            assert clo<=elo and ehi<=chi,'independent energy outside manuscript interval'
        gap=epi-epp
        lo,hi=endpoints(gap)
        assert lo>0
        center=mp.mpf('3.66704952964e-6' if frozen else '3.67139685705e-6')
        radius=mp.mpf('1.49e-18' if frozen else '5.19e-18')
        assert center-radius <=lo and hi<=center+radius,'independent gap outside published interval'
        gaps['frozen' if frozen else 'hard']=text(gap)
        records.extend((pp,pi))
    mutants=[]
    # Numeric acceptance mutant: wrong center must fail Krawczyk inclusion.
    if args.mutant:
        mutants.append(certify(False,False,ker,'shifted-center'))
    # Scientific-claim mutants: wrong sign, boundary label and asserted precision.
    hard=list(map(mp.mpf,gaps['hard']));frozen=list(map(mp.mpf,gaps['frozen']))
    assert hard[0]>0 and not (-hard[1]>0)
    assert hard[0]>frozen[1]
    assert not (mp.mpf('3.67139685705e-6')-mp.mpf('1e-22')<=hard[0] and hard[1]<=mp.mpf('3.67139685705e-6')+mp.mpf('1e-22'))
    result={'status':'CERTIFIED','trust':'mpmath.iv 60 decimal digits and exact dyadic integer matrix arithmetic; no Arb',
            'calculated_not_measured':True,'states':records,'gaps':gaps,'mutants':mutants,
            'claim_mutants_rejected':['reverse-order','swap-hard-frozen','unsupported-1e-22-radius']}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)
if __name__=='__main__':
    main()
