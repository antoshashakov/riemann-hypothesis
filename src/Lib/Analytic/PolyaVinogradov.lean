import Lib.Analytic.ZeroSymmetry

/-!
# Gauss sums of primitive characters and the Pólya–Vinogradov bound

The Gauss sum of a primitive Dirichlet character mod `q` has absolute value `√q`. For a
non-principal character mod `q`, every partial sum of its values is at most `2 √q (1 + log q)` in
absolute value.

* `New.norm_gaussSum_of_isPrimitive`: the modulus of the Gauss sum.
* `New.polya_vinogradov`: the Pólya–Vinogradov inequality.

## Relation to the literature

Known result: the Pólya–Vinogradov inequality for sums of a non-principal Dirichlet character. It is
proved here for initial intervals only, with the explicit bound `2 √q (1 + log q)`. The case of a
general character is reduced to the primitive character that induces it by a Möbius sieve. Source:
Pólya 1918, Vinogradov 1918; Davenport, Multiplicative Number Theory; Montgomery–Vaughan Thm 9.18.
-/

open Complex Finset DirichletCharacter Real ZMod ArithmeticFunction Moebius NeZero Nat

namespace New

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- The Gauss sum of a primitive Dirichlet character mod `q`, taken with the standard additive
character `x ↦ exp (2 π i x / q)` of `ZMod q`, has absolute value `√q`. -/
lemma norm_gaussSum_of_isPrimitive (hχ : χ.IsPrimitive) : ‖gaussSum χ stdAddChar‖ = √q := by
  simpa [funext hχ.fourierTransform_eq_inv_mul_gaussSum, dft_mul_const, dft_comp_neg,
    fourierTransform_eq_gaussSum_mulShift, ← AddChar.inv_mulShift, ← star_gaussSum_eq] using
    congr(√‖$(dft_dft χ) (-1)‖)

/-- The chord from `1` to the root of unity `stdAddChar k = exp (2 π i x)`, where `x = k / q` lies
in `[0, 1]`, has length at least `4 x (1 - x)`. -/
lemma four_mul_le_norm_stdAddChar_sub_one {k : ZMod q} {x : ℝ} (hx : (k.val : ℝ) = q * x)
    (hx_nonneg : 0 ≤ x) (hx_le : x ≤ 1) : 4 * (x * (1 - x)) ≤ ‖stdAddChar k - 1‖ := by
  grw [stdAddChar_apply, toCircle_eq_circleExp, Circle.coe_exp, mul_comm _ I, hx,
    norm_exp_I_mul_ofReal_sub_one, ← le_norm_self, (by field [NeZero.ne] : _ / 2 = 2 * (π / 2 * x)),
    Real.sin_two_mul, ← one_sub_mul_le_cos] <;> simp [field, pi_pos] <;>
    nlinarith [le_sin_mul hx_nonneg hx_le]

/-- For `k ≠ 0` in `ZMod q`, the sum of the powers `1, …, X` of the root of unity
`stdAddChar k = exp (2 π i k / q)` has absolute value at most `q / 2 · (1 / k + 1 / (q - k))`,
where `k` is read as its representative `k.val` in `[1, q - 1]`. -/
lemma norm_sum_stdAddChar_pow_le {k : ZMod q} (hk : k ≠ 0) (X : ℕ) :
    ‖∑ v ∈ Ioc 0 X, stdAddChar k ^ v‖ ≤ q / 2 * ((k.val : ℝ)⁻¹ + ((q - k.val : ℕ) : ℝ)⁻¹) := by
  obtain ⟨x, c, hx, d⟩ : ∃ x > (0 : ℝ), k.val = q * x ∧ 0 < 1 - x := ⟨k.val / q, by
    simp [field, val_lt, -natCast_val, hk, NeZero.ne, NeZero.pos]⟩
  grw [← Ico_add_one_add_one_eq_Ioc, geom_sum_Ico
    (injective_stdAddChar.ne hk ∘ by simp) (by simp), norm_div, norm_sub_le,
    ← four_mul_le_norm_stdAddChar_sub_one hx c.le (by linarith)]
  simp [val_le, field, ← two_mul, hx]
  norm_num

/-- The Pólya–Vinogradov inequality for a primitive Dirichlet character `χ` of modulus `q ≠ 1`:
`|∑_{1 ≤ v ≤ X} χ v| ≤ √q (1 + log q)` for all `X`. -/
lemma norm_sum_le_of_isPrimitive (hχ : χ.IsPrimitive) (hq : q ≠ 1) (X : ℕ) :
    ‖∑ v ∈ Ioc 0 X, χ v‖ ≤ √q * (1 + Real.log q) := by
  let f (n : ℕ) : ℝ := √q * q / 2 * ((n : ℝ)⁻¹ + ((q - n : ℕ) : ℝ)⁻¹)
  grw [← dft.symm_apply_apply χ]
  simp_rw [invDFT_apply, ← nsmul_eq_mul', AddChar.map_nsmul_eq_pow, ← smul_sum,
    @sum_comm _ _ ℕ, ← sum_smul, hχ.fourierTransform_eq_inv_mul_gaussSum]
  grw [norm_smul, ← sum_erase _ (a := 0) (by simp [map_zero' χ⁻¹ hq]),
    norm_sum_le_of_le _ (n := (f ·.val)) fun k hk ↦ ?_,
    ← sum_image (val_injective q).injOn, (by grind : image _ _ ⊆ range (q + 1)),
    ← harmonic_le_one_add_log]
  iterate 3 simp [f, sum_add_distrib, ← mul_sum, sum_flip fun n : ℕ ↦ (n : ℝ)⁻¹,
    harmonic, field, sum_range_succ', two_mul, NeZero.ne]
  · ring_nf
    exact le_rfl
  grw [norm_smul, norm_mul, norm_le_one, norm_gaussSum_of_isPrimitive hχ,
    norm_sum_stdAddChar_pow_le (ne_of_mem_erase hk)]
  simp only [f]
  ring_nf
  exact le_rfl

/-- A natural number `r` has at most `2 √r` divisors. -/
lemma card_divisors_le_two_mul_sqrt (r : ℕ) : (#r.divisors : ℝ) ≤ 2 * √r := by
  grw [card_le_card (t := Ioc 0 r.sqrt ∪ (Ioc 0 r.sqrt).image (r / ·)) fun d hd ↦ ?_,
    card_union_le, Finset.card_image_le, ← nat_sqrt_le_real_sqrt]
  · simp [two_mul]
  simp [zero_lt_iff] at *
  cases hd.1
  cases le_sqrt_of_eq_mul ‹_› <;> aesop

omit [NeZero q] in
/-- Möbius sieve: if `χ` mod `q = M * r` is induced by `ψ` mod `M`, then `χ v` is the sum of
`μ d • ψ v` over the common divisors `d` of `v` and `r`. -/
lemma apply_eq_sum_moebius_smul_of_changeLevel_eq {M r : ℕ} {ψ : DirichletCharacter ℂ M}
    (hr : q = M * r) (h_ind : changeLevel ⟨r, hr⟩ ψ = χ) (v : ℕ) :
    χ v = ∑ d ∈ (v.gcd r).divisors, μ d • ψ v := by
  rw [← sum_smul, ← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply, ← Int.cast_natCast]
  split <;> grind [Int.cast_natCast, apply_eq_zero_iff, changeLevel_eq_cast_of_dvd',
    coprime_mul_iff_right, isCoprime_iff_coprime]

/-- The multiples of `d > 0` in `[1, X]` are the numbers `d * e` with `1 ≤ e ≤ X / d`. -/
lemma filter_dvd_Ioc_eq_image_mul {d : ℕ} (hd : 0 < d) (X : ℕ) :
    {v ∈ Ioc 0 X | d ∣ v} = (Ioc 0 (X / d)).image fun e : ℕ ↦ d * e := by
  ext v
  simp only [mem_filter, mem_image, mem_Ioc, le_div_iff_mul_le hd, mul_comm _ d, dvd_def]
  aesop

/-- If `χ` mod `q = M * r` is induced by `ψ` mod `M`, then a partial sum of `χ` is a combination of
partial sums of `ψ`, indexed by the divisors `d` of `r`, with coefficients `μ d * ψ d`. -/
lemma sum_eq_sum_divisors_of_changeLevel_eq {M r : ℕ} {ψ : DirichletCharacter ℂ M}
    (hr : q = M * r) (h_ind : changeLevel ⟨r, hr⟩ ψ = χ) (X : ℕ) :
    ∑ v ∈ Ioc 0 X, χ v = ∑ d ∈ r.divisors, μ d * ψ d * ∑ v ∈ Ioc 0 (X / d), ψ v := by
  simp_rw [apply_eq_sum_moebius_smul_of_changeLevel_eq hr h_ind]
  rw [sum_comm' (t' := r.divisors) (s' := fun d ↦ (Ioc 0 (X / d)).image (d * ·)) (by
    rintro v ⟨⟩ <;> simp [Nat.dvd_gcd_iff, le_div_iff_mul_le, dvd_def (b := v), mul_comm]
    aesop)]
  refine sum_congr rfl fun d hd ↦ ?_
  simp [mul_sum, mul_assoc, (pos_of_mem_divisors hd).ne']

/-- The **Pólya–Vinogradov inequality** for initial intervals: for a non-principal Dirichlet
character `χ` mod `q` one has `|∑_{1 ≤ v ≤ X} χ v| ≤ 2 √q (1 + log q)` for all `X`. -/
theorem polya_vinogradov (hχ : χ ≠ 1) (X : ℕ) :
    ‖∑ v ∈ Ioc 0 X, χ v‖ ≤ 2 * √q * (1 + Real.log q) := by
  -- Apply the bound for the primitive `ψ` mod `M` that induces `χ`, once for each divisor of
  -- `r = q / M`.
  obtain ⟨M, hMq, ψ, _, hψ, h_ind⟩ := exists_isPrimitive_changeLevel_eq χ
  obtain ⟨r, hr⟩ := exists_eq_mul_right_of_dvd hMq
  have hM : M ≠ 1 := fun h ↦ hχ (by rw [← h_ind, ψ.level_one' h, map_one])
  have hM_pos : (0 : ℝ) < M := Nat.cast_pos.mpr (NeZero.pos M)
  have hM_le : (M : ℝ) ≤ q := mod_cast le_of_dvd (NeZero.pos q) hMq
  have h_term (d : ℕ) : ‖μ d * ψ d * ∑ v ∈ Ioc 0 (X / d), ψ v‖ ≤ √M * (1 + Real.log q) := by
    have hμ : ‖(μ d : ℂ)‖ ≤ 1 := by simpa using mod_cast abs_moebius_le_one (n := d)
    grw [norm_mul, norm_mul, hμ, ψ.norm_le_one, norm_sum_le_of_isPrimitive hψ hM, one_mul,
      one_mul, Real.log_le_log hM_pos hM_le]
  calc ‖∑ v ∈ Ioc 0 X, χ v‖
      ≤ #r.divisors • (√M * (1 + Real.log q)) := by
        grw [sum_eq_sum_divisors_of_changeLevel_eq hr h_ind, norm_sum_le]
        exact sum_le_card_nsmul _ _ _ fun (d : ℕ) _ ↦ h_term d
    _ ≤ 2 * √r * (√M * (1 + Real.log q)) := by grw [nsmul_eq_mul, card_divisors_le_two_mul_sqrt]
    _ = 2 * √q * (1 + Real.log q) := by
        rw [hr, Nat.cast_mul, Real.sqrt_mul hM_pos.le]
        ring

end New
