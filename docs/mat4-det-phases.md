# Mat4x4 Determinant Properties — Phase Plan

Phased plan for proving all determinant properties for `Mat4x4<T: Ring>`,
culminating in adjugate, inverse, and runtime exec wrappers.

## Phase 1: Easy det properties + helper lemmas ✔

Cofactor infrastructure and properties that delegate directly to Vec3 triple
product lemmas (swap_12, swap_23, self_zero_12, self_zero_23, linear_first).

- [x] `cofactor_vec` spec fn — signed cofactor vector for Laplace expansion
- [x] `lemma_det_as_dot` — det(m) ≡ dot(row0, cofactor_vec(row1, row2, row3))
- [x] `lemma_det_identity` — det(I) ≡ 1
- [x] `lemma_det_congruence` — row-wise eqv ⟹ det eqv
- [x] `lemma_det_swap_rows_12` — swap rows 1↔2 negates det
- [x] `lemma_det_swap_rows_23` — swap rows 2↔3 negates det
- [x] `lemma_det_zero_repeated_row_12` — row1 = row2 ⟹ det ≡ 0
- [x] `lemma_det_zero_repeated_row_23` — row2 = row3 ⟹ det ≡ 0
- [x] `lemma_det_linear_first_row` — det is linear in row 0

Helpers: `lemma_zero_alt_sum`, `lemma_det_from_zero_cofactors`,
`lemma_negate_alt_sum_4`, `lemma_flip_neg_eqv`.

---

## Phase 2: Medium det properties ◼

Properties that require new proof techniques beyond simple triple-product
delegation — cofactor linearity, row-0 involvement, and non-adjacent swaps.

- [ ] `lemma_det_scale_first_row` — det([s·r0, r1, r2, r3]) ≡ s · det(m)
- [ ] `lemma_det_zero_first_row` — det([0, r1, r2, r3]) ≡ 0
- [ ] `lemma_det_zero_repeated_row_13` — row1 = row3 ⟹ det ≡ 0
      (uses triple_self_zero_13 via cyclic + self_zero_23)
- [ ] `lemma_det_swap_rows_13` — swap rows 1↔3 negates det
      (compose: swap_12 ∘ swap_23 ∘ swap_12)
- [ ] `lemma_cofactor_vec_linear_first` — cofactor_vec additive in first arg
- [ ] `lemma_det_linear_second_row` — det is linear in row 1
- [ ] `lemma_det_scale_second_row` — det([r0, s·r1, r2, r3]) ≡ s · det(m)
- [ ] `lemma_det_zero_repeated_row_01` — row0 = row1 ⟹ det ≡ 0
      (hardest — needs bilinearity + mul_commutative cancellation)
- [ ] `lemma_det_swap_rows_01` — swap rows 0↔1 negates det
      (from zero_repeated_01 + bilinearity in rows 0,1)

---

## Phase 3: Derived det properties ◻

All remaining row-swap and zero-repeated variants, composed from Phase 2.
Plus any additional multilinearity or alternating-form lemmas.

- [ ] `lemma_det_swap_rows_02` — compose swap_01 ∘ swap_12 ∘ swap_01
- [ ] `lemma_det_swap_rows_03` — compose swap_01 ∘ swap_13 ∘ swap_01
- [ ] `lemma_det_zero_repeated_row_02` — from swap_02 or direct
- [ ] `lemma_det_zero_repeated_row_03` — from swap_03 or direct
- [ ] `lemma_det_row_operation` — det([r0, r1 + s·r0, r2, r3]) ≡ det(m)
      (adding multiple of one row to another preserves det)
- [ ] Any additional linearity/scale lemmas for rows 2, 3

---

## Phase 4: Adjugate + mat_mul_adjugate_right ◻

Define the 4×4 adjugate (classical adjoint) via signed cofactor matrix
and prove m · adj(m) ≡ det(m) · I.

- [ ] `adjugate` spec fn — 4×4 cofactor matrix (16 signed 3×3 dets)
- [ ] `lemma_mat_mul_adjugate_right` — m · adj(m) ≡ det(m) · I
      (diagonal: each row · its cofactor column = det;
       off-diagonal: row · wrong cofactor column = 0 via zero_repeated)
- [ ] `lemma_adjugate_congruence` — row-wise eqv ⟹ adjugate eqv

---

## Phase 5: Inverse + inverse_right ◻

Define inverse via adjugate / det and prove m · inv(m) ≡ I.

- [ ] `inverse` spec fn — (1/det) · adj(m), requires OrderedField
- [ ] `lemma_inverse_right` — m · inv(m) ≡ I (when det ≠ 0)
- [ ] `lemma_inverse_involution` — inv(inv(m)) ≡ m
- [ ] `lemma_det_inverse` — det(inv(m)) ≡ 1/det(m)

---

## Phase 6: Det transpose ◻

Prove det(m^T) ≡ det(m). This requires relating row-0 Laplace expansion
to column-0 expansion (or using adjugate + multiplicativity).

- [ ] `lemma_det_transpose` — det(transpose(m)) ≡ det(m)
- [ ] `lemma_det_multiplicative` — det(A · B) ≡ det(A) · det(B)
      (may be proved before or after transpose, depending on approach)

Strategy options:
  - Direct: expand det(m^T) via Laplace, relate to det(m) column expansion
  - Via adjugate: det(m^T) = det(adj(adj(m))/det(m)^2) (complex)
  - Via multiplicativity + special matrices (Gaussian elimination style)

---

## Phase 7: Left variants ◻

Mirror right-side lemmas to left-side using transpose or direct proofs.

- [ ] `lemma_mat_mul_adjugate_left` — adj(m) · m ≡ det(m) · I
      (transpose trick: apply right adjugate to m^T, use det_transpose)
- [ ] `lemma_inverse_left` — inv(m) · m ≡ I
- [ ] `lemma_adjugate_transpose` — adj(m^T) ≡ adj(m)^T (if needed)

---

## Phase 8: Runtime adjugate + cleanup ◻

Exec wrappers for adjugate, inverse, and any remaining runtime functions.

- [ ] `adjugate_exec` — RuntimeMat4x4 adjugate
- [ ] `inverse_exec` — RuntimeMat4x4 inverse (requires RuntimeRational det ≠ 0)
- [ ] Cleanup: remove any `assume(false)`, update TODO.md stats
- [ ] Update crate-level docs and module re-exports

---

## Dependencies

```
Phase 1 (done)
  └→ Phase 2 (medium det)
       └→ Phase 3 (derived det)
       └→ Phase 4 (adjugate)
            └→ Phase 5 (inverse)
            └→ Phase 6 (det transpose / multiplicative)
                 └→ Phase 7 (left variants)
                      └→ Phase 8 (runtime + cleanup)
```

## Key proof techniques

| Technique | Used in |
|---|---|
| Triple product delegation (swap, self_zero, linear) | Phases 1, 2 |
| Cofactor vec + dot product bridge | Phases 1, 2 |
| Composition of adjacent swaps | Phases 2, 3 |
| Bilinearity + mul_commutative cancellation | Phase 2 (zero_repeated_01) |
| Negate alt-sum helper | Phase 1 (swap lemmas) |
| Off-diagonal cofactor = 0 (zero_repeated) | Phase 4 (adjugate) |
| Transpose trick (apply right proof to m^T) | Phase 7 |
