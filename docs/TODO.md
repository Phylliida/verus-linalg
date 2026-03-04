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

602 verified items, 0 errors, 0 assumes/admits.

| Module | Type | Operations | Lemmas | Status |
|---|---|---|---|---|
| `vec2` | `Vec2<T>` | scale, dot, norm_sq, lerp, proj, rej, cwise_min/max | 46 | Done |
| `vec3` | `Vec3<T>` | scale, dot, norm_sq, lerp, cross, triple, proj, rej, cwise_min/max | 60+ | Done |
| `vec4` | `Vec4<T>` | scale, dot, norm_sq, lerp, cwise_min/max | 54 | Done |
| `mat2` | `Mat2x2<T>` | identity, mat_vec_mul, transpose, det, mat_mul, adjugate, inverse | 23 | Done |
| `mat3` | `Mat3x3<T>` | identity, mat_vec_mul, transpose, det, mat_mul, adjugate, inverse | 28 | Done |
| `quat` | `Quat<T>` | mul, conjugate, norm_sq, inverse, rotation, basis | 80+ | Done |
| `runtime` | `RuntimeVec2/3/4, RuntimeQuat, RuntimeMat2x2/3x3` | exec wrappers for all spec ops | 70+ | Done |

All spec types implement `Equivalence + AdditiveCommutativeMonoid + AdditiveGroup`.
Runtime types use `Ghost<SpecType<Rational>>` + `wf_spec()` pattern with exec ops ensuring `out@ == spec_fn(args@)`.

### Key proven properties

**Scale:** distributes over add, associative, identity, zero, congruence, negation interaction.
**Dot:** commutative, distributes over add, zero, scale interaction, Cauchy-Schwarz.
**Cross (Vec3 only):** anticommutative, self-zero, distributes over add, scale linearity,
orthogonality (dot(cross(a,b), a) = 0), Lagrange identity.
**Triple (Vec3 only):** self-zero, linear, antisymmetric swaps, cyclic permutation.
**Mat2x2:** transpose involution, mat_vec_mul distributes, identity multiplication,
det multiplicative, det transpose, adjugate, inverse right/left, inverse involution, det inverse.
**Mat3x3:** transpose involution, mat_vec_mul distributes, identity multiplication, determinant
sign under row swap, det zero when rows repeated, det linear in first row, det identity,
det congruence, det transpose, adjugate (via cross products), inverse right/left.

---

## Remaining work — Priority order

### P0 — Linear system solvers (next up)

Thin wrappers around existing inverse + mat_vec_mul. Directly needed by
verus-geometry for intersection point computation (Cramer's rule).

- [ ] `solve_2x2(m: Mat2x2<T: Field>, b: Vec2<T>) -> Vec2<T>` — `mat_vec_mul(inverse(m), b)`
- [ ] `solve_3x3(m: Mat3x3<T: Field>, b: Vec3<T>) -> Vec3<T>` — `mat_vec_mul(inverse(m), b)`
- [ ] Lemma: `mat_vec_mul(m, solve(m, b)) ≡ b` (correctness, when det != 0)
- [ ] Lemma: if `mat_vec_mul(m, x) ≡ b` and det != 0, then `x ≡ solve(m, b)` (uniqueness)

Estimated ~100-150 lines total. Easy — delegates to existing inverse lemmas.

Files: `mat2/ops.rs`, `mat3/ops.rs`

---

### P1 — Det multiplicative for Mat3x3

Important algebraic completeness. Unlocks det_inverse and inverse_involution
for Mat3x3 (Mat2x2 already has all of these).

- [ ] `lemma_det_multiplicative`: `det(mat_mul(a, b)) ≡ det(a).mul(det(b))`

The hardest remaining lemma. Direct expansion has many terms. Strategies:
1. Brute force: expand both sides, match via ring axioms (~500+ lines)
2. Multilinearity of det + column operations
3. Leverage existing lemmas (det_linear_first_row, row swap, etc.)

Mat2x2's `lemma_det_multiplicative` proof (in `mat2/ops.rs`) serves as a pattern
reference but is much simpler (4 terms vs 36+).

- [ ] `lemma_det_inverse`: `det(inverse(m)) ≡ recip(det(m))` — follows from det_multiplicative
- [ ] `lemma_inverse_involution`: `inverse(inverse(m)) ≡ m` — follows from det_inverse

Estimated ~600-700 lines total. Hard.

File: `mat3/ops.rs`

---

### P2 — Quaternions (port from old VerusCAD)

Needed for 3D rotations in CAD (orientation of parts, view manipulation).
The old `vcad-math` has a **complete, verified** quaternion module (~5,300 lines)
that can be ported with mechanical refactoring (replace concrete `Scalar` with
generic `T: Ring`).

Source files for porting:
- `old/VerusCAD/crates/vcad-math/src/quaternion.rs` (~4,666 lines)
- `old/VerusCAD/crates/vcad-math/src/quaternion_assoc_cases.rs` (~637 lines)

#### 2.1 Type and algebra

```
pub struct Quaternion<T: Ring> {
    pub w: T,  // scalar part
    pub x: T,  // i component
    pub y: T,  // j component
    pub z: T,  // k component
}
```

- [ ] Define `Quaternion<T: Ring>`
- [ ] Implement `Equivalence`, `AdditiveCommutativeMonoid`, `AdditiveGroup`
- [ ] `quat_mul(a, b)` — Hamilton product (NOT commutative, 16-term expansion)
- [ ] `conjugate(q)` — (w, -x, -y, -z)
- [ ] `norm_sq(q)` — w^2 + x^2 + y^2 + z^2
- [ ] `inverse(q)` — conjugate(q) / norm_sq(q) (requires Field, norm_sq != 0)
- [ ] `from_scalar(s)` — embed scalar as quaternion (s, 0, 0, 0)
- [ ] `from_vec3(v)` — embed vector as pure quaternion (0, vx, vy, vz)
- [ ] `to_vec3(q)` — extract vector part

#### 2.2 Ring structure proofs

- [ ] Lemma: `quat_mul` is associative (64 basis cases — old code has all)
- [ ] Lemma: `quat_mul` is NOT commutative (counterexample witness)
- [ ] Lemma: `quat_mul` distributes over addition (left + right)
- [ ] Lemma: one is multiplicative identity
- [ ] Basis algebra: i^2 = j^2 = k^2 = -1, ij = k, jk = i, ki = j

#### 2.3 Conjugation and norm

- [ ] Lemma: conjugate involution
- [ ] Lemma: conjugate is additive, linear over scale
- [ ] Lemma: `conjugate(quat_mul(a, b)) ≡ quat_mul(conjugate(b), conjugate(a))` (reversal)
- [ ] Lemma: `norm_sq(quat_mul(a, b)) ≡ norm_sq(a) * norm_sq(b)` (multiplicativity)
- [ ] Lemma: `norm_sq` nonnegative, zero iff q = 0
- [ ] Lemma: `quat_mul(q, conjugate(q)) ≡ from_scalar(norm_sq(q))`

#### 2.4 Inverse and division

- [ ] Lemma: `quat_mul(q, inverse(q)) ≡ from_scalar(one)` (right inverse)
- [ ] Lemma: `quat_mul(inverse(q), q) ≡ from_scalar(one)` (left inverse)
- [ ] Lemma: inverse involution
- [ ] Lemma: norm_sq(inverse(q)) = 1/norm_sq(q)

#### 2.5 Rotation via quaternion

- [ ] `rotate_vec3(q, v)` — compute `q * from_vec3(v) * conjugate(q)` and extract vec3
- [ ] Lemma: rotation preserves vector norm_sq (unit quaternion precondition)
- [ ] Lemma: rotation composition: `rotate(q1, rotate(q2, v)) ≡ rotate(q1*q2, v)`
- [ ] Lemma: rotated quaternion has zero scalar part (result is pure)

Estimated ~4,000-5,000 lines. Moderate difficulty (mechanical port, proofs exist).

Files: new `src/quat.rs` + `src/quat/ops.rs` (+ possibly `src/quat/assoc_cases.rs`)

---

### P3 — Mat4x4 (deferred)

Needed for homogeneous coordinate transformations (3D graphics, BREP).
No old code to port — write from scratch following Mat3x3 patterns.

- [ ] Define `Mat4x4<T: Ring>` with rows `row0..row3: Vec4<T>`
- [ ] Implement `Equivalence`, `AdditiveCommutativeMonoid`, `AdditiveGroup`
- [ ] `identity()`, `mat_vec_mul`, `mat_mul`, `transpose`, `det`
- [ ] Key lemmas: transpose involution, multiply identity, det multiplicativity
- [ ] Lemma: det sign under row permutations
- [ ] Adjugate + inverse (when needed)

Estimated ~2,000-3,000 lines. Easy-Medium (tedious, more components).

Files: new `src/mat4.rs` + `src/mat4/ops.rs`

---

### P4 — Affine transformations (deferred)

Combine rotation, translation, and scaling. Needs Mat3x3 + quaternions first.

- [ ] `AffineTransform3<T>` — linear part (Mat3x3) + translation (Vec3)
- [ ] `apply_point`, `apply_vec`, `compose`, `identity`
- [ ] Lemma: compose is associative, identity is neutral
- [ ] `RigidTransform3` — quaternion rotation + translation subset
- [ ] Lemma: rigid transforms preserve distances

---

### P5 — Extended vector operations (deferred)

Small utilities, easy to add on demand.

- [ ] `outer(a, b) -> Mat3x3<T>` — outer/tensor product
- [ ] `skew(v) -> Mat3x3<T>` — skew-symmetric matrix (skew(v)*w = cross(v,w))
- [ ] Homogeneous coordinate conversions (Point3 <-> Vec4)

---

### P6 — Eigenvalues and decompositions (long-term)

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
det identity, det congruence, det transpose, mat_mul_adjugate right/left,
inverse right/left. Plus helper lemmas: 3-factor product rearrangements,
sub_add_swap, adjugate_transpose_rows.

### Phase 3 — Vec2/Vec3/Vec4 (DONE)

Complete vector type suites: 46 + 60+ + 54 = 160+ verified lemmas.
Scale, dot, norm_sq, lerp, cross, triple, proj, rej, cwise_min/max,
Cauchy-Schwarz, Lagrange identity, and more.

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
| Linear solvers | Easy | Thin wrappers around inverse |
| Det multiplicative 3x3 | Hard | Many terms, longest single proof |
| Quaternion port | Moderate | Mechanical refactor, all proofs exist |
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
| **Linear solvers** | P0 | Intersection point computation in verus-geometry |
| **Det multiplicative 3x3** | P1 | Algebraic completeness (det_inverse, inverse_involution) |
| **Quaternions** | P2 | 3D rotations for CAD view/part orientation |
| **Mat4x4** | P3 | Homogeneous coordinates, 3D transforms |
| **Affine transforms** | P4 | Unified transform framework for BREP kernel |
| **Extended ops** | P5 | Projection matrices, Rodrigues rotation |
