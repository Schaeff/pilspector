use crate::ast::*;

pub trait Fold: Sized {
    fn fold<F: Folder>(self, f: &mut F, ctx: &Pil) -> Result<Self, F::Error>;
}

impl Fold for Add {
    fn fold<F: Folder>(self, f: &mut F, ctx: &Pil) -> Result<Self, F::Error> {
        f.fold_add(self, ctx)
    }
}

impl Fold for Sub {
    fn fold<F: Folder>(self, f: &mut F, ctx: &Pil) -> Result<Self, F::Error> {
        f.fold_sub(self, ctx)
    }
}

impl Fold for Mul {
    fn fold<F: Folder>(self, f: &mut F, ctx: &Pil) -> Result<Self, F::Error> {
        f.fold_mul(self, ctx)
    }
}

impl Fold for Neg {
    fn fold<F: Folder>(self, f: &mut F, ctx: &Pil) -> Result<Self, F::Error> {
        f.fold_neg(self, ctx)
    }
}

impl Fold for Public {
    fn fold<F: Folder>(self, f: &mut F, ctx: &Pil) -> Result<Self, F::Error> {
        f.fold_public(self, ctx)
    }
}

impl Fold for Exp {
    fn fold<F: Folder>(self, f: &mut F, ctx: &Pil) -> Result<Self, F::Error> {
        f.fold_exp(self, ctx)
    }
}

impl Fold for Cm {
    fn fold<F: Folder>(self, f: &mut F, ctx: &Pil) -> Result<Self, F::Error> {
        f.fold_cm(self, ctx)
    }
}

impl Fold for Const {
    fn fold<F: Folder>(self, f: &mut F, ctx: &Pil) -> Result<Self, F::Error> {
        f.fold_const(self, ctx)
    }
}

impl Fold for Number {
    fn fold<F: Folder>(self, f: &mut F, ctx: &Pil) -> Result<Self, F::Error> {
        f.fold_number(self, ctx)
    }
}

pub trait Folder: Sized {
    type Error;

    fn fold_pil(&mut self, p: Pil) -> Result<Pil, Self::Error> {
        fold_pil(self, p)
    }

    fn fold_polynomial_identity(
        &mut self,
        i: PolIdentity,
        ctx: &Pil,
        index: usize,
    ) -> Result<PolIdentity, Self::Error> {
        fold_polynomial_identity(self, i, ctx, index)
    }

    fn fold_plookup_identity(
        &mut self,
        i: PlookupIdentity,
        ctx: &Pil,
        index: usize,
    ) -> Result<PlookupIdentity, Self::Error> {
        fold_plookup_identity(self, i, ctx, index)
    }

    fn fold_permutation_identity(
        &mut self,
        i: PermutationIdentity,
        ctx: &Pil,
        index: usize,
    ) -> Result<PermutationIdentity, Self::Error> {
        fold_permutation_identity(self, i, ctx, index)
    }

    fn fold_connection_identity(
        &mut self,
        i: ConnectionIdentity,
        ctx: &Pil,
        index: usize,
    ) -> Result<ConnectionIdentity, Self::Error> {
        fold_connection_identity(self, i, ctx, index)
    }

    fn fold_expression(&mut self, e: Expression, ctx: &Pil) -> Result<Expression, Self::Error> {
        fold_expression(self, e, ctx)
    }

    fn fold_expression_id(
        &mut self,
        id: ExpressionId,
        ctx: &Pil,
    ) -> Result<ExpressionId, Self::Error> {
        fold_expression_id(self, id, ctx)
    }

    fn fold_expression_wrapper<E: Expr + Fold>(
        &mut self,
        e: ExpressionWrapper<E>,
        ctx: &Pil,
    ) -> Result<ExpressionWrapper<E>, Self::Error> {
        fold_expression_wrapper(self, e, ctx)
    }

    fn fold_add(&mut self, values: Add, ctx: &Pil) -> Result<Add, Self::Error> {
        fold_add(self, values, ctx)
    }

    fn fold_sub(&mut self, values: Sub, ctx: &Pil) -> Result<Sub, Self::Error> {
        fold_sub(self, values, ctx)
    }

    fn fold_mul(&mut self, values: Mul, ctx: &Pil) -> Result<Mul, Self::Error> {
        fold_mul(self, values, ctx)
    }

    fn fold_public(&mut self, public: Public, ctx: &Pil) -> Result<Public, Self::Error> {
        fold_public(self, public, ctx)
    }

    fn fold_neg(&mut self, value: Neg, ctx: &Pil) -> Result<Neg, Self::Error> {
        fold_neg(self, value, ctx)
    }

    fn fold_cm(&mut self, cm: Cm, ctx: &Pil) -> Result<Cm, Self::Error> {
        fold_cm(self, cm, ctx)
    }

    fn fold_exp(&mut self, exp: Exp, ctx: &Pil) -> Result<Exp, Self::Error> {
        fold_exp(self, exp, ctx)
    }

    fn fold_const(&mut self, c: Const, ctx: &Pil) -> Result<Const, Self::Error> {
        fold_const(self, c, ctx)
    }

    fn fold_number(&mut self, c: Number, ctx: &Pil) -> Result<Number, Self::Error> {
        fold_number(self, c, ctx)
    }

    fn fold_name(&mut self, c: Name, ctx: &Pil) -> Result<Name, Self::Error> {
        fold_reference_key(self, c, ctx)
    }

    fn fold_polynomial(
        &mut self,
        c: ShiftedPolynomial,
        ctx: &Pil,
    ) -> Result<ShiftedPolynomial, Self::Error> {
        fold_polynomial(self, c, ctx)
    }

    fn fold_reference(&mut self, r: Polynomials, ctx: &Pil) -> Result<Polynomials, Self::Error> {
        fold_reference(self, r, ctx)
    }

    fn fold_reference_inner<Id>(
        &mut self,
        inner: ReferenceInner<Id>,
        ctx: &Pil,
    ) -> Result<ReferenceInner<Id>, Self::Error> {
        fold_reference_inner(self, inner, ctx)
    }

    fn fold_public_cell(&mut self, cell: PublicCell, ctx: &Pil) -> Result<PublicCell, Self::Error> {
        fold_public_cell(self, cell, ctx)
    }
}

pub fn fold_pil<F: Folder>(f: &mut F, p: Pil) -> Result<Pil, F::Error> {
    unimplemented!()
}

pub fn fold_polynomial_identity<F: Folder>(
    f: &mut F,
    i: PolIdentity,
    ctx: &Pil,
    _index: usize,
) -> Result<PolIdentity, F::Error> {
    unimplemented!()
}

pub fn fold_plookup_identity<F: Folder>(
    f: &mut F,
    i: PlookupIdentity,
    ctx: &Pil,
    _index: usize,
) -> Result<PlookupIdentity, F::Error> {
    unimplemented!()
}

pub fn fold_permutation_identity<F: Folder>(
    f: &mut F,
    i: PermutationIdentity,
    ctx: &Pil,
    _index: usize,
) -> Result<PermutationIdentity, F::Error> {
    unimplemented!()
}

pub fn fold_connection_identity<F: Folder>(
    f: &mut F,
    i: ConnectionIdentity,
    ctx: &Pil,
    _index: usize,
) -> Result<ConnectionIdentity, F::Error> {
    unimplemented!()
}

pub fn fold_expression<F: Folder>(
    f: &mut F,
    e: Expression,
    ctx: &Pil,
) -> Result<Expression, F::Error> {
    Ok(match e {
        Expression::Public(w) => Expression::Public(f.fold_expression_wrapper(w, ctx)?),
        Expression::Neg(w) => Expression::Neg(f.fold_expression_wrapper(w, ctx)?),
        Expression::Exp(w) => Expression::Exp(f.fold_expression_wrapper(w, ctx)?),
        Expression::Add(w) => Expression::Add(f.fold_expression_wrapper(w, ctx)?),
        Expression::Sub(w) => Expression::Sub(f.fold_expression_wrapper(w, ctx)?),
        Expression::Mul(w) => Expression::Mul(f.fold_expression_wrapper(w, ctx)?),
        Expression::Cm(w) => Expression::Cm(f.fold_expression_wrapper(w, ctx)?),
        Expression::Number(w) => Expression::Number(f.fold_expression_wrapper(w, ctx)?),
        Expression::Const(w) => Expression::Const(f.fold_expression_wrapper(w, ctx)?),
    })
}

pub fn fold_expression_wrapper<F: Folder, E: Expr + Fold>(
    f: &mut F,
    e: ExpressionWrapper<E>,
    ctx: &Pil,
) -> Result<ExpressionWrapper<E>, F::Error> {
    Ok(ExpressionWrapper {
        inner: e.inner.fold(f, ctx)?,
        ..e
    })
}

pub fn fold_add<F: Folder>(f: &mut F, add: Add, ctx: &Pil) -> Result<Add, F::Error> {
    Ok(Add {
        values: Box::new(
            add.values
                .into_iter()
                .map(|v| f.fold_expression(v, ctx))
                .collect::<Result<Vec<_>, _>>()?
                .try_into()
                .unwrap(),
        ),
    })
}

pub fn fold_sub<F: Folder>(f: &mut F, sub: Sub, ctx: &Pil) -> Result<Sub, F::Error> {
    Ok(Sub {
        values: Box::new(
            sub.values
                .into_iter()
                .map(|v| f.fold_expression(v, ctx))
                .collect::<Result<Vec<_>, _>>()?
                .try_into()
                .unwrap(),
        ),
    })
}

pub fn fold_mul<F: Folder>(f: &mut F, mul: Mul, ctx: &Pil) -> Result<Mul, F::Error> {
    Ok(Mul {
        values: Box::new(
            mul.values
                .into_iter()
                .map(|v| f.fold_expression(v, ctx))
                .collect::<Result<Vec<_>, _>>()?
                .try_into()
                .unwrap(),
        ),
    })
}

pub fn fold_public<F: Folder>(f: &mut F, public: Public, ctx: &Pil) -> Result<Public, F::Error> {
    unimplemented!()
}

pub fn fold_neg<F: Folder>(f: &mut F, neg: Neg, ctx: &Pil) -> Result<Neg, F::Error> {
    Ok(Neg {
        values: Box::new(
            neg.values
                .into_iter()
                .map(|v| f.fold_expression(v, ctx))
                .collect::<Result<Vec<_>, _>>()?
                .try_into()
                .unwrap(),
        ),
    })
}

pub fn fold_cm<F: Folder>(f: &mut F, cm: Cm, ctx: &Pil) -> Result<Cm, F::Error> {
    unimplemented!()
}

pub fn fold_exp<F: Folder>(f: &mut F, exp: Exp, ctx: &Pil) -> Result<Exp, F::Error> {
    unimplemented!()
}

pub fn fold_const<F: Folder>(f: &mut F, c: Const, ctx: &Pil) -> Result<Const, F::Error> {
    unimplemented!()
}

pub fn fold_polynomial<F: Folder>(
    _: &mut F,
    p: ShiftedPolynomial,
    _: &Pil,
) -> Result<ShiftedPolynomial, F::Error> {
    Ok(p)
}
pub fn fold_expression_id<F: Folder>(
    f: &mut F,
    id: ExpressionId,
    ctx: &Pil,
) -> Result<ExpressionId, F::Error> {
    Ok(id)
}

pub fn fold_number<F: Folder>(_f: &mut F, c: Number, _ctx: &Pil) -> Result<Number, F::Error> {
    Ok(c)
}

pub fn fold_reference_key<F: Folder>(_f: &mut F, name: Name, _ctx: &Pil) -> Result<Name, F::Error> {
    Ok(name)
}

pub fn fold_reference<F: Folder>(
    f: &mut F,
    r: Polynomials,
    ctx: &Pil,
) -> Result<Polynomials, F::Error> {
    Ok(match r {
        Polynomials::CmP(i) => Polynomials::CmP(f.fold_reference_inner(i, ctx)?),
        Polynomials::ConstP(i) => Polynomials::ConstP(f.fold_reference_inner(i, ctx)?),
        Polynomials::ImP(i) => Polynomials::ImP(f.fold_reference_inner(i, ctx)?),
    })
}

pub fn fold_reference_inner<F: Folder, Id>(
    _f: &mut F,
    r: ReferenceInner<Id>,
    _ctx: &Pil,
) -> Result<ReferenceInner<Id>, F::Error> {
    Ok(r)
}

pub fn fold_public_cell<F: Folder>(
    f: &mut F,
    cell: PublicCell,
    ctx: &Pil,
) -> Result<PublicCell, F::Error> {
    unimplemented!()
}
