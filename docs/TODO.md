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

195+ verified items, 0 errors, 0 assumes/admits.

| Module | Type | Operations | Lemmas | Status |
|---|---|---|---|---|
| `vec2` | `Vec2<T>` | scale, dot, norm_sq, lerp, proj, rej, cwise_min/max | 46 | Done |
| `vec3` | `Vec3<T>` | scale, dot, norm_sq, lerp, cross, triple, proj, rej, cwise_min/max | 60+ | Done |
| `vec4` | `Vec4<T>` | scale, dot, norm_sq, lerp, cwise_min/max | 54 | Done |
| `mat3` | `Mat3x3<T>` | identity, mat_vec_mul, transpose, det, mat_mul | 13 | Done |

All types implement `Equivalence + AdditiveCommutativeMonoid + AdditiveGroup`.

### Key proven properties

**Scale:** distributes over add, associative, identity, zero, congruence, negation interaction.
**Dot:** commutative, distributes over add, zero, scale interaction, Cauchy-Schwarz.
**Cross (Vec3 only):** anticommutative, self-zero, distributes over add, scale linearity,
orthogonality (dot(cross(a,b), a) ≡ 0), Lagrange identity.
**Triple (Vec3 only):** self-zero, linear, antisymmetric swaps, cyclic permutation.
**Mat3x3:** transpose involution, mat_vec_mul distributes, identity multiplication, determinant
sign under row swap, det zero when rows repeated, det linear in first row.

---

## Phase 1 — Mat2x2

A 2x2 matrix is needed for 2D transformations and orient2d decomposition.

- [ ] Define `Mat2x2<T: Ring>` with rows `row0: Vec2<T>`, `row1: Vec2<T>`
- [ ] Implement `Equivalence`, `AdditiveCommutativeMonoid`, `AdditiveGroup`
- [ ] `identity()` — 2x2 identity matrix
- [ ] `mat_vec_mul(m, v)` — matrix-vector multiplication
- [ ] `mat_mul(a, b)` — matrix-matrix multiplication
- [ ] `transpose(m)` — transpose
- [ ] `det(m)` — determinant (ad - bc)
- [ ] Lemma: transpose involution
- [ ] Lemma: mat_vec_mul distributes over vector addition
- [ ] Lemma: mat_vec_mul identity
- [ ] Lemma: det(transpose(m)) ≡ det(m)
- [ ] Lemma: det(mat_mul(a, b)) ≡ det(a) * det(b) (multiplicativity)
- [ ] Lemma: det row swap negates sign

---

## Phase 2 — Mat4x4

Needed for homogeneous coordinate transformations (3D graphics, BREP).

- [ ] Define `Mat4x4<T: Ring>` with rows `row0..row3: Vec4<T>`
- [ ] Implement `Equivalence`, `AdditiveCommutativeMonoid`, `AdditiveGroup`
- [ ] `identity()`, `mat_vec_mul`, `mat_mul`, `transpose`, `det`
- [ ] Key lemmas: transpose involution, multiply identity, det multiplicativity
- [ ] Lemma: det sign under row permutations

---

## Phase 3 — Matrix inverse (requires Field)

Needed for solving linear systems, coordinate transforms, etc.

### 3.1 Mat2x2 inverse

- [ ] `inverse(m: Mat2x2<T: Field>) -> Mat2x2<T>` (when det ≠ 0)
- [ ] Lemma: `mat_mul(m, inverse(m)) ≡ identity()` (when det ≠ 0)
- [ ] Lemma: `mat_mul(inverse(m), m) ≡ identity()`
- [ ] Lemma: `inverse(inverse(m)) ≡ m`
- [ ] Lemma: `det(inverse(m)) ≡ recip(det(m))`

### 3.2 Mat3x3 inverse

- [ ] Cofactor matrix / adjugate
- [ ] `inverse(m: Mat3x3<T: Field>) -> Mat3x3<T>` via adjugate / det
- [ ] Same lemma suite as Mat2x2
- [ ] Cramer's rule as a corollary

### 3.3 Solving linear systems

- [ ] `solve_2x2(m, b)` — solve Ax = b for 2x2
- [ ] `solve_3x3(m, b)` — solve Ax = b for 3x3
- [ ] Lemma: solution satisfies `mat_vec_mul(m, x) ≡ b`
- [ ] Lemma: solution is unique when det ≠ 0

---

## Phase 4 — Quaternions

Needed for 3D rotations in CAD (orientation of parts, view manipulation).
The old vcad-math had a full quaternion module.

### 4.1 Quaternion type

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

### 4.2 Quaternion algebra

- [ ] `quat_mul(a, b)` — Hamilton product (NOT commutative)
- [ ] `conjugate(q)` — (w, -x, -y, -z)
- [ ] `norm_sq(q)` — w² + x² + y² + z²
- [ ] `inverse(q)` — conjugate(q) / norm_sq(q) (for Field, when norm_sq ≠ 0)
- [ ] `from_scalar(s)` — embed scalar as quaternion (s, 0, 0, 0)
- [ ] `from_vec3(v)` — embed vector as pure quaternion (0, vx, vy, vz)
- [ ] `to_vec3(q)` — extract vector part

### 4.3 Quaternion lemmas

- [ ] Lemma: `quat_mul` is associative
- [ ] Lemma: `quat_mul` is NOT commutative (counterexample witness)
- [ ] Lemma: `quat_mul` distributes over addition
- [ ] Lemma: `conjugate(conjugate(q)) ≡ q` (involution)
- [ ] Lemma: `conjugate(quat_mul(a, b)) ≡ quat_mul(conjugate(b), conjugate(a))` (reversal)
- [ ] Lemma: `norm_sq(quat_mul(a, b)) ≡ norm_sq(a) * norm_sq(b)` (multiplicativity)
- [ ] Lemma: `quat_mul(q, inverse(q)) ≡ from_scalar(one)` (for nonzero)
- [ ] Lemma: `quat_mul(q, conjugate(q)) ≡ from_scalar(norm_sq(q))`

### 4.4 Rotation via quaternion

- [ ] `rotate_vec3(q, v)` — compute `q * from_vec3(v) * conjugate(q)` and extract vec3
- [ ] Lemma: rotation preserves vector length (norm_sq)
- [ ] Lemma: rotation preserves dot product
- [ ] Lemma: rotation composition: rotate(q1, rotate(q2, v)) ≡ rotate(q1*q2, v)
- [ ] Lemma: unit quaternion rotation is an isometry

---

## Phase 5 — Affine transformations

Combine rotation, translation, and scaling in a unified framework.

### 5.1 Affine transform type

```
pub struct AffineTransform3<T: Ring> {
    pub linear: Mat3x3<T>,   // rotation + scale + shear
    pub translation: Vec3<T>, // translation offset
}
```

- [ ] Define `AffineTransform3<T>`
- [ ] `apply_point(t, p: Point3<T>) -> Point3<T>` — linear * p + translation
- [ ] `apply_vec(t, v: Vec3<T>) -> Vec3<T>` — linear * v (vectors ignore translation)
- [ ] `compose(t1, t2)` — composition of transforms
- [ ] `identity()` — identity transform

### 5.2 Affine transform lemmas

- [ ] Lemma: compose is associative
- [ ] Lemma: identity is neutral element
- [ ] Lemma: apply_point(compose(t1, t2), p) ≡ apply_point(t1, apply_point(t2, p))
- [ ] Lemma: if linear part is orthogonal, transform preserves distances

### 5.3 Rigid transforms (rotation + translation only)

- [ ] `RigidTransform3` — quaternion rotation + translation
- [ ] Lemma: rigid transforms preserve distances
- [ ] Lemma: rigid transforms preserve orientation (det > 0)
- [ ] Conversion: RigidTransform3 ↔ AffineTransform3

---

## Phase 6 — Extended vector operations

### 6.1 Outer product (tensor product)

- [ ] `outer(a: Vec3<T>, b: Vec3<T>) -> Mat3x3<T>` — a ⊗ b
- [ ] Lemma: `mat_vec_mul(outer(a, b), v) ≡ scale(dot(b, v), a)`
- [ ] Lemma: `trace(outer(a, b)) ≡ dot(a, b)`
- [ ] Useful for: projection matrices, Householder reflections

### 6.2 Skew-symmetric matrix from Vec3

- [ ] `skew(v: Vec3<T>) -> Mat3x3<T>` — matrix such that skew(v) * w ≡ cross(v, w)
- [ ] Lemma: `mat_vec_mul(skew(v), w) ≡ cross(v, w)`
- [ ] Lemma: `skew(v)` is antisymmetric: `transpose(skew(v)) ≡ neg(skew(v))`
- [ ] Useful for: Rodrigues' rotation formula, angular velocity

### 6.3 Homogeneous coordinates

- [ ] `to_homogeneous(p: Point3<T>) -> Vec4<T>` — (x, y, z, 1)
- [ ] `from_homogeneous(v: Vec4<T>) -> Point3<T>` — (x/w, y/w, z/w) (requires Field, w ≠ 0)
- [ ] `to_homogeneous_vec(v: Vec3<T>) -> Vec4<T>` — (x, y, z, 0)
- [ ] Lemma: round-trip `from_homogeneous(to_homogeneous(p)) ≡ p`
- [ ] Useful for: perspective projection, NURBS, projective geometry

---

## Phase 7 — Eigenvalues and decompositions (long-term)

These are needed for advanced operations (principal curvatures, mass properties)
but are complex to verify. Lower priority.

### 7.1 Characteristic polynomial

- [ ] `char_poly_2x2(m) -> (T, T, T)` — coefficients of det(m - λI)
- [ ] `char_poly_3x3(m) -> (T, T, T, T)`
- [ ] Lemma: Cayley-Hamilton theorem (m satisfies its own char. polynomial)

### 7.2 Eigenvalues for symmetric matrices

- [ ] 2x2 symmetric eigenvalues (closed form via quadratic formula)
- [ ] 3x3 symmetric eigenvalues (Cardano's formula or iterative, harder to verify)
- [ ] Spectral theorem: symmetric matrix has real eigenvalues

### 7.3 SVD / Polar decomposition

- [ ] Very long-term. Probably defer until actively needed.

---

## Proof strategy notes

### Pattern: component-wise proofs

Most vector/matrix proofs expand to component-level algebra and then
apply ring lemmas. This is mechanical but verbose. The current codebase
handles this well — follow the same pattern for new types.

### Pattern: lifting lemmas across dimensions

Vec2/Vec3/Vec4 have parallel lemma suites (scale, dot, norm_sq, etc.).
Currently each is proven independently. Consider:
- Could a macro or proof-by-analogy reduce duplication? (Verus limitation: probably not)
- At minimum, keep the naming convention identical across dimensions

### Difficulty estimates

| Item | Difficulty | Notes |
|---|---|---|
| Mat2x2 basics | Easy | Same pattern as Mat3x3, fewer components |
| Mat4x4 basics | Easy-Medium | Same pattern, more components, more tedious |
| Matrix inverse 2x2 | Medium | Need to prove adjugate formula correct |
| Matrix inverse 3x3 | Medium-Hard | Cofactor expansion, 9 minors |
| Quaternion algebra | Medium | Hamilton product has 16 terms, not commutative |
| Quaternion rotation proofs | Hard | Rotation preserving norm needs norm_sq multiplicativity |
| Affine transforms | Medium | Composition is matrix multiply + translation bookkeeping |
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

| Milestone | Phases | What it enables |
|---|---|---|
| **M1: Mat2x2** | 1 | 2D transforms, orient2d as det(Mat2x2) |
| **M2: Mat4x4** | 2 | Homogeneous coordinates, 3D transforms |
| **M3: Matrix inverse** | 3 | Linear system solving, coordinate transforms |
| **M4: Quaternions** | 4 | 3D rotations for CAD view/part orientation |
| **M5: Affine transforms** | 5 | Unified transform framework for BREP kernel |
| **M6: Extended ops** | 6 | Projection matrices, Rodrigues rotation |

**M1 and M3 are highest priority** — downstream geometry predicates
(intersection point computation) need 2x2/3x3 system solving.
**M4 is important for CAD UX** (view rotation, part placement).
