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

    fn fold_pil(&mut self, _p: Pil) -> Result<Pil, Self::Error> {
        unimplemented!()
    }

    fn fold_polynomial_identity(
        &mut self,
        _i: PolIdentity,
        _ctx: &Pil,
        _index: usize,
    ) -> Result<PolIdentity, Self::Error> {
        unimplemented!()
    }

    fn fold_plookup_identity(
        &mut self,
        _i: PlookupIdentity,
        _ctx: &Pil,
        _index: usize,
    ) -> Result<PlookupIdentity, Self::Error> {
        unimplemented!()
    }

    fn fold_permutation_identity(
        &mut self,
        _i: PermutationIdentity,
        _ctx: &Pil,
        _index: usize,
    ) -> Result<PermutationIdentity, Self::Error> {
        unimplemented!()
    }

    fn fold_connection_identity(
        &mut self,
        _i: ConnectionIdentity,
        _ctx: &Pil,
        _index: usize,
    ) -> Result<ConnectionIdentity, Self::Error> {
        unimplemented!()
    }

    fn fold_expression(&mut self, e: Expression, ctx: &Pil) -> Result<Expression, Self::Error> {
        fold_expression(self, e, ctx)
    }

    fn fold_expression_id(
        &mut self,
        _id: ExpressionId,
        _ctx: &Pil,
    ) -> Result<ExpressionId, Self::Error> {
        unimplemented!()
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

    fn fold_name(&mut self, _c: Name, _ctx: &Pil) -> Result<Name, Self::Error> {
        unimplemented!()
    }

    fn fold_polynomial(
        &mut self,
        _c: ShiftedPolynomial,
        _ctx: &Pil,
    ) -> Result<ShiftedPolynomial, Self::Error> {
        unimplemented!()
    }

    fn fold_reference(&mut self, _r: Polynomials, _ctx: &Pil) -> Result<Polynomials, Self::Error> {
        unimplemented!()
    }

    fn fold_reference_inner<Id>(
        &mut self,
        _inner: ReferenceInner<Id>,
        _ctx: &Pil,
    ) -> Result<ReferenceInner<Id>, Self::Error> {
        unimplemented!()
    }

    fn fold_public_cell(&mut self, _cell: PublicCell, _ctx: &Pil) -> Result<PublicCell, Self::Error> {
        unimplemented!()
    }
}

fn fold_expression<F: Folder>(f: &mut F, e: Expression, ctx: &Pil) -> Result<Expression, F::Error> {
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

fn fold_expression_wrapper<F: Folder, E: Expr + Fold>(
    f: &mut F,
    e: ExpressionWrapper<E>,
    ctx: &Pil,
) -> Result<ExpressionWrapper<E>, F::Error> {
    Ok(ExpressionWrapper {
        inner: e.inner.fold(f, ctx)?,
        ..e
    })
}

fn fold_add<F: Folder>(f: &mut F, add: Add, ctx: &Pil) -> Result<Add, F::Error> {
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

fn fold_sub<F: Folder>(f: &mut F, sub: Sub, ctx: &Pil) -> Result<Sub, F::Error> {
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

fn fold_mul<F: Folder>(f: &mut F, mul: Mul, ctx: &Pil) -> Result<Mul, F::Error> {
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

fn fold_public<F: Folder>(_f: &mut F, _public: Public, _ctx: &Pil) -> Result<Public, F::Error> {
    unimplemented!()
}

fn fold_neg<F: Folder>(f: &mut F, neg: Neg, ctx: &Pil) -> Result<Neg, F::Error> {
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

fn fold_cm<F: Folder>(_f: &mut F, _cm: Cm, _ctx: &Pil) -> Result<Cm, F::Error> {
    unimplemented!()
}

fn fold_exp<F: Folder>(_f: &mut F, _exp: Exp, _ctx: &Pil) -> Result<Exp, F::Error> {
    unimplemented!()
}

fn fold_const<F: Folder>(_f: &mut F, _c: Const, _ctx: &Pil) -> Result<Const, F::Error> {
    unimplemented!()
}

fn fold_number<F: Folder>(_f: &mut F, c: Number, _ctx: &Pil) -> Result<Number, F::Error> {
    Ok(c)
}


