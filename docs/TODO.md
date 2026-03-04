# verus-linalg — Implementation TODO

Formally verified linear algebra primitives in Rust + Verus, parameterized
over any `Ring` (from verus-algebra).

This crate provides the **vector and matrix types** that verus-geometry and
downstream crates build on. Pure spec-level — no runtime exec code here.

## Crate layering

```
verus-algebra (Ring, OrderedRing, Field traits + lemmas)
  └→ verus-linalg              ← this crate (vectors, matrices)
       └→ verus-geometry       (predicates: orientation, intersection, etc.)
       └→ verus-topology       (combinatorial mesh)
       └→ verus-brep-kernel    (BREP: curves, surfaces, evaluation)
```

## What we have now

533 verified items, 0 errors, 0 assumes/admits.

| Module | Type | Operations | Lemmas | Status |
|---|---|---|---|---|
| `vec2` | `Vec2<T>` | scale, dot, norm_sq, lerp, proj, rej, cwise_min/max | 46 | Done |
| `vec3` | `Vec3<T>` | scale, dot, norm_sq, lerp, cross, triple, proj, rej, cwise_min/max | 60+ | Done |
| `vec4` | `Vec4<T>` | scale, dot, norm_sq, lerp, cwise_min/max | 54 | Done |
| `mat2` | `Mat2x2<T>` | identity, mat_vec_mul, transpose, det, mat_mul, adjugate, inverse | 25 | Done |
| `mat3` | `Mat3x3<T>` | identity, mat_vec_mul, transpose, det, mat_mul, adjugate, inverse | 30 | Done |
| `mat4` | `Mat4x4<T>` | identity, mat_vec_mul, transpose, det, mat_mul | 30 | Done |
| `quat` | `Quat<T>` | mul, conjugate, norm_sq, inverse, rotation, basis | 80+ | Done |
| `runtime` | `RuntimeVec2/3/4, RuntimeQuat, RuntimeMat2x2/3x3/4x4` | exec wrappers for all spec ops | 70+ | Done |

All spec types implement `Equivalence + AdditiveCommutativeMonoid + AdditiveGroup`.
Runtime types use `Ghost<SpecType<Rational>>` + `wf_spec()` pattern with exec ops ensuring `out@ == spec_fn(args@)`.

### Key proven properties

**Scale:** distributes over add, associative, identity, zero, congruence, negation interaction.
**Dot:** commutative, distributes over add, zero, scale interaction, Cauchy-Schwarz.
**Cross (Vec3 only):** anticommutative, self-zero, distributes over add, scale linearity,
orthogonality (dot(cross(a,b), a) = 0), Lagrange identity.
**Triple (Vec3 only):** self-zero, linear, antisymmetric swaps, cyclic permutation.
**Mat2x2:** transpose involution, mat_vec_mul distributes, identity multiplication,
det multiplicative, det transpose, adjugate, inverse right/left, inverse involution, det inverse,
mat_mul associative, transpose-of-product.
**Mat3x3:** transpose involution, mat_vec_mul distributes, identity multiplication, determinant
sign under row swap, det zero when rows repeated, det linear in first row, det identity,
det congruence, det transpose, adjugate (via cross products), inverse right/left,
mat_mul associative, transpose-of-product.

---

## Remaining work — Priority order

### P0 — Cross-checking properties (spec bug catchers)

These properties cross-check that spec definitions (mat_mul, transpose,
conjugate) are mutually consistent. A subtle sign error or index swap in
any one definition would be caught by these.

- [x] **`mat_mul` associativity (Mat2x2)**: `mat_mul(A, mat_mul(B, C)) ≡ mat_mul(mat_mul(A, B), C)`
- [x] **`mat_mul` associativity (Mat3x3)**: same property
- [x] **`transpose(mat_mul(A, B)) ≡ mat_mul(transpose(B), transpose(A))`** (Mat2x2)
- [x] **`transpose(mat_mul(A, B)) ≡ mat_mul(transpose(B), transpose(A))`** (Mat3x3)
- [x] **`conjugate(mul(a, b)) ≡ mul(conjugate(b), conjugate(a))`** (Quat anti-automorphism)

Strategy: component-wise expansion + ring axioms. Mat2x2 has 2x2=4 entries
each with ~8 terms. Mat3x3 has 3x3=9 entries each with ~27 terms — larger but
still mechanical. Quaternion conjugate-of-product has 4 components with ~16 terms each.

Files: `mat2/ops.rs`, `mat3/ops.rs`, `quat/conjugate.rs`

---

### P1 — Linear system solvers

Thin wrappers around existing inverse + mat_vec_mul. Directly needed by
verus-geometry for intersection point computation (Cramer's rule).

- [x] `solve_2x2(m: Mat2x2<T: Field>, b: Vec2<T>) -> Vec2<T>` — `mat_vec_mul(inverse(m), b)`
- [x] `solve_3x3(m: Mat3x3<T: Field>, b: Vec3<T>) -> Vec3<T>` — `mat_vec_mul(inverse(m), b)`
- [x] Lemma: `mat_vec_mul(m, solve(m, b)) ≡ b` (correctness, when det != 0)
- [x] Lemma: if `mat_vec_mul(m, x) ≡ b` and det != 0, then `x ≡ solve(m, b)` (uniqueness)

Estimated ~100-150 lines total. Easy — delegates to existing inverse lemmas.

Files: `mat2/ops.rs`, `mat3/ops.rs`

---

### P2 — Mat4x4 (DONE — core)

Homogeneous coordinate transformations (3D graphics, BREP).

- [x] Define `Mat4x4<T: Ring>` with rows `row0..row3: Vec4<T>`
- [x] `identity()`, `mat_vec_mul`, `mat_mul`, `transpose`, `det` (Laplace expansion)
- [x] Key lemmas: transpose involution, identity multiplication, mat_mul associative,
  transpose-of-product, det identity, det congruence, mat_vec_mul distributes/scales
- [x] `RuntimeMat4x4` exec wrapper
- [ ] Adjugate + inverse (deferred until needed)
- [ ] Det swap rows, det zero repeated, det linear, det transpose, det multiplicative (deferred)

Files: `src/mat4.rs`, `src/mat4/ops.rs`, `src/runtime/mat4.rs`

---

### P3 — Affine transformations (deferred)

Combine rotation, translation, and scaling. Needs Mat3x3 + quaternions first.

- [ ] `AffineTransform3<T>` — linear part (Mat3x3) + translation (Vec3)
- [ ] `apply_point`, `apply_vec`, `compose`, `identity`
- [ ] Lemma: compose is associative, identity is neutral
- [ ] `RigidTransform3` — quaternion rotation + translation subset
- [ ] Lemma: rigid transforms preserve distances

---

### P4 — Extended vector operations (deferred)

Small utilities, easy to add on demand.

- [ ] `outer(a, b) -> Mat3x3<T>` — outer/tensor product
- [ ] `skew(v) -> Mat3x3<T>` — skew-symmetric matrix (skew(v)*w = cross(v,w))
- [ ] Homogeneous coordinate conversions (Point3 <-> Vec4)

---

### P5 — Eigenvalues and decompositions (long-term)

- [ ] Characteristic polynomial for 2x2, 3x3
- [ ] Cayley-Hamilton theorem
- [ ] Eigenvalues for symmetric matrices
- [ ] SVD / Polar decomposition

---

## Completed phases

### Phase 1 — Mat2x2 (DONE)

Full implementation with 23 lemmas including:
identity, mat_vec_mul, transpose, det, mat_mul, adjugate, inverse,
transpose involution, det transpose, det multiplicative, det swap rows,
det identity, det congruence, inverse right/left, inverse involution, det inverse.

### Phase 2 — Mat3x3 core (DONE)

Full implementation with 28 lemmas including:
identity, mat_vec_mul, transpose, det, mat_mul, adjugate (via cross products), inverse,
transpose involution, det swap rows, det zero repeated rows, det linear first row,
det identity, det congruence, det transpose, det multiplicative, mat_mul_adjugate right/left,
inverse right/left. Plus helper lemmas: 3-factor product rearrangements,
sub_add_swap, adjugate_transpose_rows.

### Phase 3 — Vec2/Vec3/Vec4 (DONE)

Complete vector type suites: 46 + 60+ + 54 = 160+ verified lemmas.
Scale, dot, norm_sq, lerp, cross, triple, proj, rej, cwise_min/max,
Cauchy-Schwarz, Lagrange identity, and more.

### Phase 4 — Quaternions (DONE)

Full quaternion module: 80+ verified items across 9 files.
Type, algebra (Equivalence + AdditiveGroup), Hamilton product, associativity (64 basis cases),
conjugate (involution, additive, scale, anti-automorphism), norm_sq (multiplicative, nonneg),
inverse (right/left, involution), rotation (preserves norm, pure output), basis algebra.

### Phase 5 — Runtime types (DONE)

RuntimeVec2/3/4, RuntimeQuat, RuntimeMat2x2/3x3/4x4 with exec wrappers for all spec ops.
70+ exec functions, each ensuring `out@ == spec_fn(args@)`. Uses `Ghost<SpecType<Rational>>`
pattern with `wf_spec()`. verus-geometry migrated to import from verus-linalg.

### Phase 6 — Mat4x4 (DONE)

Full 4x4 matrix module: 32 new verified items.
Type, identity, mat_vec_mul, transpose, det (Laplace expansion via Vec3 triple product),
mat_mul, drop_x/y/z/w helpers. Lemmas: transpose involution, mat_vec_mul distributes/scales/zero,
basis dot products, identity multiplication, det identity, det congruence,
mat_mul associative, transpose-of-product.
RuntimeMat4x4 with identity, mat_vec_mul, transpose, det, mat_mul exec functions.

---

## Proof strategy notes

### Pattern: component-wise proofs

Most vector/matrix proofs expand to component-level algebra and then
apply ring lemmas. This is mechanical but verbose. The current codebase
handles this well — follow the same pattern for new types.

### Pattern: cross product adjugate (Mat3x3)

The 3x3 adjugate has a natural expression via cross products:
columns of adj(m) = cross(r1,r2), cross(r2,r0), cross(r0,r1).
This made the adjugate product proofs much cleaner than direct
cofactor expansion (~130 lines vs estimated 300-400).

### Pattern: transpose trick (Mat3x3 left inverse)

To prove adj(m)*m = det(m)*I, apply the right adjugate proof to m^T
and use dot_commutative + adjugate_transpose_rows to relate entries.
This avoids duplicating the entire 9-entry expansion.

### Difficulty estimates

| Item | Difficulty | Notes |
|---|---|---|
| Cross-checking properties (P0) | Medium | Mechanical component expansion, verbose |
| Linear solvers | Easy | Thin wrappers around inverse |
| Mat4x4 basics | Easy-Medium | Same pattern, more components |
| Affine transforms | Medium | Composition is mat_mul + translation |
| Eigenvalues | Hard | Requires polynomial root reasoning |
| SVD | Very Hard | Existence proof is non-trivial |

---

## Trust surface

| Trusted | Why |
|---|---|
| `vstd` | Verus standard library |
| `verus-algebra` axioms | Ring/Field axiom soundness |

Everything in this crate: verified, no `unsafe`, no `assume`.
Enforced by `--forbid-trusted-escapes` in CI.

---

## Milestones

| Milestone | Priority | What it enables |
|---|---|---|
| **Cross-checking properties** | P0 | Catches spec-level bugs in mat_mul, transpose, conjugate |
| **Linear solvers** | P1 | Intersection point computation in verus-geometry |
| **Mat4x4** | P2 | Homogeneous coordinates, 3D transforms |
| **Affine transforms** | P3 | Unified transform framework for BREP kernel |
| **Extended ops** | P4 | Projection matrices, Rodrigues rotation |
| **Eigenvalues** | P5 | Characteristic polynomial, Cayley-Hamilton |
