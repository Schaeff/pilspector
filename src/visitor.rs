use crate::ast::*;

pub type Result<E> = std::result::Result<(), E>;

pub trait Visit {
    fn visit<V: Visitor>(&self, v: &mut V, ctx: &Pil) -> Result<V::Error>;
}

impl Visit for Add {
    fn visit<V: Visitor>(&self, v: &mut V, ctx: &Pil) -> Result<V::Error> {
        v.visit_add(self, ctx)
    }
}

impl Visit for Sub {
    fn visit<V: Visitor>(&self, v: &mut V, ctx: &Pil) -> Result<V::Error> {
        v.visit_sub(self, ctx)
    }
}

impl Visit for Mul {
    fn visit<V: Visitor>(&self, v: &mut V, ctx: &Pil) -> Result<V::Error> {
        v.visit_mul(self, ctx)
    }
}

impl Visit for Neg {
    fn visit<V: Visitor>(&self, v: &mut V, ctx: &Pil) -> Result<V::Error> {
        v.visit_neg(self, ctx)
    }
}

impl Visit for Public {
    fn visit<V: Visitor>(&self, v: &mut V, ctx: &Pil) -> Result<V::Error> {
        v.visit_public(self, ctx)
    }
}

impl Visit for Exp {
    fn visit<V: Visitor>(&self, v: &mut V, ctx: &Pil) -> Result<V::Error> {
        v.visit_exp(self, ctx)
    }
}

impl Visit for Cm {
    fn visit<V: Visitor>(&self, v: &mut V, ctx: &Pil) -> Result<V::Error> {
        v.visit_cm(self, ctx)
    }
}

impl Visit for Const {
    fn visit<V: Visitor>(&self, v: &mut V, ctx: &Pil) -> Result<V::Error> {
        v.visit_const(self, ctx)
    }
}

impl Visit for Number {
    fn visit<V: Visitor>(&self, v: &mut V, ctx: &Pil) -> Result<V::Error> {
        v.visit_number(self, ctx)
    }
}

pub trait Visitor: Sized {
    type Error;

    fn visit_pil(&mut self, p: &Pil) -> Result<Self::Error> {
        visit_pil(self, p)
    }

    fn visit_polynomial_identity(
        &mut self,
        i: &PolIdentity,
        ctx: &Pil,
        index: usize,
    ) -> Result<Self::Error> {
        visit_polynomial_identity(self, i, ctx, index)
    }

    fn visit_plookup_identity(
        &mut self,
        i: &PlookupIdentity,
        ctx: &Pil,
        index: usize,
    ) -> Result<Self::Error> {
        visit_plookup_identity(self, i, ctx, index)
    }

    fn visit_permutation_identity(
        &mut self,
        i: &PermutationIdentity,
        ctx: &Pil,
        index: usize,
    ) -> Result<Self::Error> {
        visit_permutation_identity(self, i, ctx, index)
    }

    fn visit_connection_identity(
        &mut self,
        i: &ConnectionIdentity,
        ctx: &Pil,
        index: usize,
    ) -> Result<Self::Error> {
        visit_connection_identity(self, i, ctx, index)
    }

    fn visit_expression(&mut self, e: &Expression, ctx: &Pil) -> Result<Self::Error> {
        visit_expression(self, e, ctx)
    }

    fn visit_expression_id(&mut self, id: &ExpressionId, ctx: &Pil) -> Result<Self::Error> {
        visit_expression_id(self, id, ctx)
    }

    fn visit_expression_wrapper<E: Expr + Visit>(
        &mut self,
        e: &ExpressionWrapper<E>,
        ctx: &Pil,
    ) -> Result<Self::Error> {
        visit_expression_wrapper(self, e, ctx)
    }

    fn visit_add(&mut self, values: &Add, ctx: &Pil) -> Result<Self::Error> {
        visit_add(self, values, ctx)
    }

    fn visit_sub(&mut self, values: &Sub, ctx: &Pil) -> Result<Self::Error> {
        visit_sub(self, values, ctx)
    }

    fn visit_mul(&mut self, values: &Mul, ctx: &Pil) -> Result<Self::Error> {
        visit_mul(self, values, ctx)
    }

    fn visit_exp(&mut self, exp: &Exp, ctx: &Pil) -> Result<Self::Error> {
        visit_exp(self, exp, ctx)
    }

    fn visit_public(&mut self, public: &Public, ctx: &Pil) -> Result<Self::Error> {
        visit_public(self, public, ctx)
    }

    fn visit_neg(&mut self, value: &Neg, ctx: &Pil) -> Result<Self::Error> {
        visit_neg(self, value, ctx)
    }

    fn visit_cm(&mut self, cm: &Cm, ctx: &Pil) -> Result<Self::Error> {
        visit_cm(self, cm, ctx)
    }

    fn visit_const(&mut self, c: &Const, ctx: &Pil) -> Result<Self::Error> {
        visit_const(self, c, ctx)
    }

    fn visit_number(&mut self, c: &Number, ctx: &Pil) -> Result<Self::Error> {
        visit_number(self, c, ctx)
    }

    fn visit_next(&mut self, next: &bool, ctx: &Pil) -> Result<Self::Error> {
        visit_next(self, next, ctx)
    }

    fn visit_reference_key(&mut self, c: &ReferenceKey, ctx: &Pil) -> Result<Self::Error> {
        visit_reference_key(self, c, ctx)
    }

    fn visit_indexed_reference_key(
        &mut self,
        c: &IndexedReferenceKey,
        ctx: &Pil,
    ) -> Result<Self::Error> {
        visit_indexed_reference_key(self, c, ctx)
    }

    fn visit_reference(&mut self, r: &Reference, ctx: &Pil) -> Result<Self::Error> {
        visit_reference(self, r, ctx)
    }

    fn visit_reference_inner<Id>(
        &mut self,
        inner: &ReferenceInner<Id>,
        ctx: &Pil,
    ) -> Result<Self::Error> {
        visit_reference_inner(self, inner, ctx)
    }

    fn visit_public_cell(&mut self, cell: &PublicCell, ctx: &Pil) -> Result<Self::Error> {
        visit_public_cell(self, cell, ctx)
    }
}

pub fn visit_pil<V: Visitor>(v: &mut V, p: &Pil) -> Result<V::Error> {
    let ctx = p;

    for public_cell in &p.publics {
        v.visit_public_cell(public_cell, ctx)?;
    }

    for (key, r) in &p.references {
        v.visit_reference_key(key, ctx)?;
        v.visit_reference(r, ctx)?;
    }

    for (index, identity) in p.pol_identities.iter().enumerate() {
        v.visit_polynomial_identity(identity, ctx, index)?;
    }

    for (index, identity) in p.plookup_identities.iter().enumerate() {
        v.visit_plookup_identity(identity, ctx, index)?;
    }

    for (index, identity) in p.permutation_identities.iter().enumerate() {
        v.visit_permutation_identity(identity, ctx, index)?;
    }

    for (index, identity) in p.connection_identities.iter().enumerate() {
        v.visit_connection_identity(identity, ctx, index)?;
    }

    Ok(())
}

pub fn visit_polynomial_identity<V: Visitor>(
    v: &mut V,
    i: &PolIdentity,
    ctx: &Pil,
    _index: usize,
) -> Result<V::Error> {
    v.visit_expression(&ctx.expressions[i.e.0], ctx)
}

pub fn visit_plookup_identity<V: Visitor>(
    v: &mut V,
    i: &PlookupIdentity,
    ctx: &Pil,
    _index: usize,
) -> Result<V::Error> {
    if let Some(ref id) = i.sel_f {
        v.visit_expression_id(id, ctx)?;
    }

    for id in &i.f {
        v.visit_expression_id(id, ctx)?;
    }

    if let Some(ref id) = i.sel_t {
        v.visit_expression_id(id, ctx)?;
    }

    for id in &i.t {
        v.visit_expression_id(id, ctx)?;
    }
    Ok(())
}

pub fn visit_permutation_identity<V: Visitor>(
    v: &mut V,
    i: &PermutationIdentity,
    ctx: &Pil,
    _index: usize,
) -> Result<V::Error> {
    if let Some(ref id) = i.sel_f {
        v.visit_expression_id(id, ctx)?;
    }

    for id in &i.f {
        v.visit_expression_id(id, ctx)?;
    }

    if let Some(ref id) = i.sel_t {
        v.visit_expression_id(id, ctx)?;
    }

    for id in &i.t {
        v.visit_expression_id(id, ctx)?;
    }
    Ok(())
}

pub fn visit_connection_identity<V: Visitor>(
    v: &mut V,
    i: &ConnectionIdentity,
    ctx: &Pil,
    _index: usize,
) -> Result<V::Error> {
    for id in &i.pols {
        v.visit_expression_id(id, ctx)?;
    }

    for id in &i.connections {
        v.visit_expression_id(id, ctx)?;
    }

    Ok(())
}

pub fn visit_expression<V: Visitor>(v: &mut V, e: &Expression, ctx: &Pil) -> Result<V::Error> {
    match e {
        Expression::Public(w) => {
            v.visit_expression_wrapper(w, ctx)?;
        }
        Expression::Neg(w) => {
            v.visit_expression_wrapper(w, ctx)?;
        }
        Expression::Exp(w) => {
            v.visit_expression_wrapper(w, ctx)?;
        }
        Expression::Add(w) => {
            v.visit_expression_wrapper(w, ctx)?;
        }
        Expression::Sub(w) => {
            v.visit_expression_wrapper(w, ctx)?;
        }
        Expression::Mul(w) => {
            v.visit_expression_wrapper(w, ctx)?;
        }
        Expression::Cm(w) => {
            v.visit_expression_wrapper(w, ctx)?;
        }
        Expression::Number(w) => {
            v.visit_expression_wrapper(w, ctx)?;
        }
        Expression::Const(w) => {
            v.visit_expression_wrapper(w, ctx)?;
        }
    };

    Ok(())
}

pub fn visit_expression_wrapper<V: Visitor, E: Expr + Visit>(
    v: &mut V,
    e: &ExpressionWrapper<E>,
    ctx: &Pil,
) -> Result<V::Error> {
    e.inner.visit(v, ctx)
}

pub fn visit_add<V: Visitor>(v: &mut V, values: &Add, ctx: &Pil) -> Result<V::Error> {
    for value in values.values.iter() {
        v.visit_expression(value, ctx)?;
    }
    Ok(())
}

pub fn visit_sub<V: Visitor>(v: &mut V, sub: &Sub, ctx: &Pil) -> Result<V::Error> {
    for value in sub.values.iter() {
        v.visit_expression(value, ctx)?;
    }
    Ok(())
}

pub fn visit_mul<V: Visitor>(v: &mut V, mul: &Mul, ctx: &Pil) -> Result<V::Error> {
    for value in mul.values.iter() {
        v.visit_expression(value, ctx)?;
    }
    Ok(())
}

pub fn visit_exp<V: Visitor>(v: &mut V, exp: &Exp, ctx: &Pil) -> Result<V::Error> {
    v.visit_expression(&ctx.expressions[exp.id.0], ctx)
}

pub fn visit_public<V: Visitor>(v: &mut V, public: &Public, ctx: &Pil) -> Result<V::Error> {
    v.visit_public_cell(&ctx.publics[public.id.0], ctx)
}

pub fn visit_neg<V: Visitor>(v: &mut V, values: &Neg, ctx: &Pil) -> Result<V::Error> {
    for value in values.values.iter() {
        v.visit_expression(value, ctx)?;
    }
    Ok(())
}

pub fn visit_cm<V: Visitor>(v: &mut V, cm: &Cm, ctx: &Pil) -> Result<V::Error> {
    let (indexed_reference_key, reference_inner) = ctx.get_cm_reference(cm);

    v.visit_indexed_reference_key(&indexed_reference_key, ctx)?;
    v.visit_reference_inner(reference_inner, ctx)?;
    v.visit_next(&cm.next, ctx)
}

pub fn visit_const<V: Visitor>(v: &mut V, c: &Const, ctx: &Pil) -> Result<V::Error> {
    let (indexed_reference_key, reference_inner) = ctx.get_const_reference(c);

    v.visit_indexed_reference_key(&indexed_reference_key, ctx)?;
    v.visit_reference_inner(reference_inner, ctx)?;
    v.visit_next(&c.next, ctx)
}

pub fn visit_indexed_reference_key<V: Visitor>(
    v: &mut V,
    k: &IndexedReferenceKey,
    ctx: &Pil,
) -> Result<V::Error> {
    v.visit_reference_key(&k.key.clone(), ctx)
}
pub fn visit_expression_id<V: Visitor>(
    v: &mut V,
    id: &ExpressionId,
    ctx: &Pil,
) -> Result<V::Error> {
    v.visit_expression(&ctx.expressions[id.0], ctx)
}

pub fn visit_number<V: Visitor>(_v: &mut V, _c: &Number, _ctx: &Pil) -> Result<V::Error> {
    Ok(())
}

pub fn visit_next<V: Visitor>(_v: &mut V, _c: &bool, _ctx: &Pil) -> Result<V::Error> {
    Ok(())
}

pub fn visit_reference_key<V: Visitor>(
    _v: &mut V,
    _c: &ReferenceKey,
    _ctx: &Pil,
) -> Result<V::Error> {
    Ok(())
}

pub fn visit_reference<V: Visitor>(v: &mut V, r: &Reference, ctx: &Pil) -> Result<V::Error> {
    match r {
        Reference::CmP(i) => {
            v.visit_reference_inner(i, ctx)?;
        }
        Reference::ConstP(i) => {
            v.visit_reference_inner(i, ctx)?;
        }
        Reference::ImP(i) => {
            v.visit_reference_inner(i, ctx)?;
        }
    };

    Ok(())
}

pub fn visit_reference_inner<V: Visitor, Id>(
    _v: &mut V,
    _i: &ReferenceInner<Id>,
    _ctx: &Pil,
) -> Result<V::Error> {
    Ok(())
}

pub fn visit_public_cell<V: Visitor>(v: &mut V, cell: &PublicCell, ctx: &Pil) -> Result<V::Error> {
    v.visit_cm(
        &Cm {
            id: cell.pol_id,
            next: false,
        },
        ctx,
    )
}
