"""Exact compressed checks for a prescribed-block CPQR completion candidate.

No whole wide matrix is materialized. Completion columns are algebraic:
L(:,j)*sqrt(D_j/t), repeated t times. Their pair products are rational.
These checks are research certificates, not a substitute for the Lean pivot law.
"""
from __future__ import annotations
from fractions import Fraction as F

from structselect.volume_exact import _ldl


def parameters(m):
    if type(m) is not int or m<2:
        raise ValueError('integer m>=2 required')
    k=m*m
    eps=F(4*k-1,4*k+1)
    c=F(2*m,4*k+1)
    alpha=F(1,2*k)
    t=32*k**3
    return k,eps,c,alpha,t,k+k*t


def triangular_block(m):
    k,eps,c,alpha,_,_=parameters(m)
    diagonal=[alpha*eps**i for i in range(k)]
    r=[[diagonal[i] if i==j else -c*diagonal[i] if i<j else F()
        for j in range(k)] for i in range(k)]
    return r,diagonal


def compressed_certificate(m, *, max_dimension=64):
    k,eps,c,alpha,t,n=parameters(m)
    if type(max_dimension) is not int or max_dimension<0:
        raise ValueError('nonnegative integer dimension budget required')
    if k>max_dimension:
        return {'status':'dimension_budget_exhausted','certified':False,
                'm':m,'k':k,'n':n,'required_dimension':k}
    r,diagonal=triangular_block(m)
    gram=[[sum(r[i][q]*r[j][q] for q in range(k)) for j in range(k)] for i in range(k)]
    complement=[[F(i==j)-gram[i][j] for j in range(k)] for i in range(k)]
    factor=_ldl(complement)
    if factor is None:
        raise ArithmeticError('completion complement is not positive definite')
    lower,weights=factor
    reconstructed=[[sum(lower[i][q]*weights[q]*lower[j][q] for q in range(k))
                    for j in range(k)] for i in range(k)]
    if reconstructed!=complement:
        raise ArithmeticError('exact completion identity failed')
    energies=[weights[q]*sum(lower[i][q]**2 for i in range(k))/t for q in range(k)]
    min_margin=None
    for prefix in range(k):
        pivot=diagonal[prefix]**2
        for j in range(prefix+1,k):
            residual=sum(r[i][j]**2 for i in range(prefix,k))
            gap=pivot-residual
            if gap<=0:
                raise ArithmeticError('leading triangular pivot dominance failed')
            min_margin=gap if min_margin is None else min(min_margin,gap)
        gap=pivot-max(energies)
        if gap<=0:
            raise ArithmeticError('completion column bound failed')
        min_margin=gap if min_margin is None else min(min_margin,gap)
    # Exact back-substitution R*x=e_last; no explicit inverse.
    x=[F() for _ in range(k)]
    for i in reversed(range(k)):
        x[i]=(F(i==k-1)-sum(r[i][j]*x[j] for j in range(i+1,k)))/diagonal[i]
    image=[sum(r[i][j]*x[j] for j in range(k)) for i in range(k)]
    if image!=[F(i==k-1) for i in range(k)]:
        raise ArithmeticError('inverse-energy witness solve failed')
    closed=c*(1+c)**(k-2)/diagonal[-1]
    if x[0]!=closed:
        raise ArithmeticError('inverse-entry closed form failed')
    return {'status':'exact_compressed_completion','certified':True,
            'm':m,'k':k,'n':n,'repetitions':t,'epsilon':eps,'coupling':c,
            'triangular':r,'completion_lower':lower,'completion_weights':weights,
            'completion_column_energies':energies,
            'minimum_pivot_margin':min_margin,'inverse_energy':sum(v*v for v in x),
            'witness':x,'inverse_entry':x[0],
            'scope':'exact compressed completion and coordinate-tail comparisons; '
                    'all-parameter Lean adverse-family theorem remains open'}


def growth_parameters(m):
    """Scalar-only bound check; does not construct or certify the whole frame."""
    k,eps,c,alpha,t,n=parameters(m)
    bernoulli=1-k*(1-eps)
    lower=F(2*m,3)*F(4,3)**(m-1)
    if not (eps>0 and eps<1 and bernoulli>F(1,2) and
            c>=F(1,3*m) and c*c+eps*eps<1):
        raise ArithmeticError('candidate scalar hypothesis failed')
    return {'status':'exact_scalar_bounds_only','frame_certified':False,
            'm':m,'k':k,'n':n,'bernoulli_diagonal_ratio_lower':bernoulli,
            'inverse_lower_candidate':lower,
            'exceeds_named_polynomial_if_family_proved':lower>max(n**3,k**3,(k*(n-k+1))**2)}
