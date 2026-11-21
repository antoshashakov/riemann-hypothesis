import PrincipalHeightCounts
import ExceptionalCharacterHeight
import RegularCharacterHeight

/-!
# Two character counts at conductor one

This reduction was found through Principia's collaborative RH project. It
specializes Levent Alpöge's finite character sums. A regular-prime descent
at 3 and 7 eliminates the trivial character in every positive twist.
-/

noncomputable section
namespace Principia.Ordinary.QuadraticSeven

open NumberField Polynomial

private abbrev L := CyclotomicField 7 ℚ
abbrev K := (X^2 + C ((7:ℕ):ℚ) : ℚ[X]).SplittingField

instance : NumberField K := NumberField.of_module_finite ℚ K

private theorem cyclo : IsCyclotomicExtension ({7}:Set ℕ) ℚ L := by
  exact CyclotomicField.isCyclotomicExtension 7 ℚ

/-- The quadratic Gaussian period explicitly splits X²+7. -/
theorem embedding : Nonempty (K →ₐ[ℚ] L) := by
  letI := cyclo
  let z := IsCyclotomicExtension.zeta 7 ℚ L
  have hz : IsPrimitiveRoot z 7 := IsCyclotomicExtension.zeta_spec 7 ℚ L
  have hsum : 1+z+z^2+z^3+z^4+z^5+z^6=0 := by
    simpa [Finset.sum_range_succ] using hz.geom_sum_eq_zero (by decide : 1<7)
  let v := 1+2*(z+z^2+z^4)
  have hv : v^2+7=0 := by
    calc v^2+7 = 4*(z^2-z+2)*(1+z+z^2+z^3+z^4+z^5+z^6) := by dsimp [v]; ring
         _ = 0 := by rw [hsum,mul_zero]
  have hf : (X^2 + C (7:ℚ) : ℚ[X]).map (algebraMap ℚ L) =
      (X-C v)*(X+C v) := by
    have hv' : (7:L) = -v^2 := by linear_combination hv
    calc _ = (X:L[X])^2+C (7:L) := by simp
         _ = _ := by rw [hv',map_neg,map_pow]; ring
  exact ⟨Polynomial.SplittingField.lift _ (hf ▸ (Splits.X_sub_C v).mul (Splits.X_add_C v))⟩

private theorem abs_bound {D : ℕ} (h : D^3 ∣ 7^5) : D ≤ 7 := by
  have hD : D ∣ 7^5 := dvd_trans (dvd_pow_self D (by decide : (3:ℕ) ≠ 0)) h
  obtain ⟨a,ha,rfl⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 7)).mp hD
  interval_cases a <;> norm_num at *

/-- Any quadratic subfield of Q(zeta_7) has class number one. -/
theorem class_number_of_embedding (F : Type) [Field F] [NumberField F]
    (hF : Module.finrank ℚ F = 2) (i : F →ₐ[ℚ] L) : classNumber F = 1 := by
  letI := cyclo
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  letI : Algebra F L := i.toRingHom.toAlgebra
  letI : IsScalarTower ℚ F L := IsScalarTower.of_algebraMap_eq fun r => (i.commutes r).symm
  have hL : Module.finrank ℚ L = 6 := by
    rw [IsCyclotomicExtension.Rat.finrank 7 L,Nat.totient_prime (by decide : Nat.Prime 7)]
  have hdeg : Module.finrank F L = 3 := by
    have h := Module.finrank_mul_finrank ℚ F L
    rw [hL,hF] at h
    omega
  have hdL : (discr L).natAbs = 7^5 := by
    rw [IsCyclotomicExtension.Rat.discr_prime 7 L]
    norm_num
  have ht := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) L (𝓞 L)
  rw [hdL,hdeg] at ht
  have hd := abs_bound (D:=(discr F).natAbs) (ht ▸ dvd_mul_left _ _)
  have hi : ((discr F).natAbs:ℤ) ≤ 7 := by exact_mod_cast hd
  have ha : |discr F| ≤ 7 := by simpa only [Int.natCast_natAbs] using hi
  have hdR : |((discr F):ℝ)| ≤ 7 := by exact_mod_cast ha
  have hr := InfinitePlace.card_add_two_mul_card_eq_rank F
  rw [hF] at hr
  have hc : InfinitePlace.nrComplexPlaces F = 0 ∨ InfinitePlace.nrComplexPlaces F = 1 := by omega
  apply classNumber_eq_one_iff.mpr
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [hF]
  rcases hc with hc|hc <;> rw [hc] <;> norm_num [Nat.factorial] <;>
    nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi-3)]

/- The quadratic-degree argument is from the original archive, CMFieldExponentialBounds.primesex. -/
open Polynomial in
private theorem finrank_quadratic_splitting_field (p : ℕ) (hp : 0 < p) (L : Type) [Field L] [Algebra ℚ L]
    [h : IsSplittingField ℚ L (X ^ 2 + C (p : ℚ) : ℚ[X])] : Module.finrank ℚ L = 2 := by
  set f : ℚ[X] := X ^ 2 + C (p : ℚ) with hf
  have hdeg : f.natDegree = 2 := by
    rw [hf]
    compute_degree!
  have hmon : f.Monic := by
    rw [hf]
    monicity!
  have hpq : (0 : ℚ) < p := by exact_mod_cast hp
  have hnoroot : ∀ x : ℚ, ¬ f.IsRoot x := by
    intro x hx
    rw [hf] at hx
    simp [Polynomial.IsRoot] at hx
    nlinarith [sq_nonneg x]
  have hirr : Irreducible f :=
    Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) hnoroot
  have hspl := IsSplittingField.splits L f
  have hdeg0 : (f.map (algebraMap ℚ L)).degree ≠ 0 := by
    rw [Polynomial.degree_map, Polynomial.degree_eq_natDegree hmon.ne_zero, hdeg]
    decide
  obtain ⟨α, hα⟩ := hspl.exists_eval_eq_zero hdeg0
  have haeval : aeval α f = 0 := by
    rw [aeval_def, ← eval_map]
    exact hα
  have hmin : f = minpoly ℚ α := minpoly.eq_of_irreducible_of_monic hirr haeval hmon
  have hint : IsIntegral ℚ α := ⟨f, hmon, by rw [← aeval_def]; exact haeval⟩
  have hfin : Module.finrank ℚ (IntermediateField.adjoin ℚ {α}) = 2 := by
    rw [IntermediateField.adjoin.finrank hint, ← hmin, hdeg]
  have htop : IntermediateField.adjoin ℚ {α} = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : y ∈ Algebra.adjoin ℚ (f.rootSet L) := by
      rw [IsSplittingField.adjoin_rootSet L f]
      trivial
    have hle : Algebra.adjoin ℚ (f.rootSet L) ≤ (IntermediateField.adjoin ℚ {α}).toSubalgebra := by
      apply Algebra.adjoin_le
      intro β hβ
      rw [Polynomial.mem_rootSet] at hβ
      have e1 := hβ.2
      have e2 := haeval
      rw [hf] at e1 e2
      simp at e1 e2
      have : (β - α) * (β + α) = 0 := by linear_combination e1 - e2
      rcases mul_eq_zero.mp this with h | h
      · have hb : β = α := by linear_combination h
        rw [hb]
        exact IntermediateField.mem_adjoin_simple_self ℚ α
      · have hb : β = -α := by linear_combination h
        rw [hb]
        exact neg_mem (IntermediateField.mem_adjoin_simple_self ℚ α)
    exact hle hy
  rw [← IntermediateField.finrank_top', ← htop, hfin]



theorem class_number : classNumber K = 1 := by
  obtain ⟨i⟩ := embedding
  exact class_number_of_embedding K (@finrank_quadratic_splitting_field 7 (by decide) K _ _
    (Polynomial.IsSplittingField.splittingField _)) i

end Principia.Ordinary.QuadraticSeven
end

noncomputable section
namespace Principia.Ordinary.TwoCharacterCounts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

theorem order_one : ordC PChar.one = 1 := by
  change orderOf (1 : DirichletCharacter ℂ 1) = 1
  exact orderOf_one

theorem degree_one : (AbF.ofChar PChar.one).deg = 1 := by
  change (1 : DirichletCharacter ℂ 1).toUnitHom.ker.index = 1
  apply Subgroup.index_eq_one.mpr
  exact Subsingleton.elim _ _

theorem least_quadratic_prime : pK PChar.one = 7 := by
  let S := {p : ℕ | p.Prime ∧ p%4=3 ∧ 7≤p ∧ p.Coprime 1}
  have h7 : 7 ∈ S := by decide
  change sInf S = 7
  exact le_antisymm (Nat.sInf_le h7) ((Nat.sInf_mem ⟨7,h7⟩).2.2.1)

theorem least_auxiliary_prime : pOne PChar.one = 3 := by
  unfold pOne
  rw [order_one,least_quadratic_prime]
  change sInf {p : ℕ | p.Prime ∧ p ≡ 1 [MOD ordCompl[2] 1] ∧ p.Coprime 14} = 3
  let S := {p : ℕ | p.Prime ∧ p ≡ 1 [MOD ordCompl[2] 1] ∧ p.Coprime 14}
  have h3 : 3 ∈ S := by
    change Nat.Prime 3 ∧ 3 ≡ 1 [MOD 1 / 2 ^ (Nat.factorization 1) 2] ∧ (3:ℕ).Coprime 14
    simp only [Nat.factorization_one,Finsupp.zero_apply,pow_zero,Nat.div_one]
    decide
  refine le_antisymm (Nat.sInf_le h3) ?_
  have h := Nat.sInf_mem (s:=S) ⟨3,h3⟩
  have h2 : sInf S ≠ 2 := fun p => (by decide : ¬ (2:ℕ).Coprime 14) (p ▸ h.2.2)
  have hp : 2 ≤ sInf S := h.1.two_le
  change 3 ≤ sInf S
  omega

theorem auxiliary_class_number : classNumber (Kstar 7) = 1 := Principia.Ordinary.QuadraticSeven.class_number

/-- The only class number entering the exceptional set is h(-7)=1. -/
theorem exceptional_set :
    Bchi PChar.one = {3,7} := by
  let H (p : ℕ) := classNumber (Kstar p)
  have hs : hStar PChar.one = 1 := (congrArg H least_quadratic_prime).trans auxiliary_class_number
  unfold Bchi
  rw [order_one,least_quadratic_prime,least_auxiliary_prime,hs]
  change insert 3 ((7*3 : ℕ).primeFactors.erase 2) = {3,7}
  rw [Nat.primeFactors_mul (by decide) (by decide),
    (by decide : Nat.Prime 7).primeFactors,(by decide : Nat.Prime 3).primeFactors]
  decide

private theorem exists_closure : ∃ (Q : Type) (_ : Field Q) (_ : CharZero Q), IsAlgClosure ℚ Q := by
  refine ⟨AlgebraicClosure ℚ, inferInstance, inferInstance,
    (isAlgClosure_iff ℚ (AlgebraicClosure ℚ)).2 ⟨inferInstance, ?_⟩⟩
  have h := AlgebraicClosure.isAlgebraic ℚ
  convert h using 1
  exact Subsingleton.elim (α := Algebra ℚ (AlgebraicClosure ℚ)) _ _

private theorem card_small (S : Finset Nat.Primes) (n : ℕ) (h : ∀ l ∈ S, (l : ℕ) ≤ n) : S.card ≤ n := by
  have key : S.card ≤ (Finset.Icc 1 n).card := by
    apply Finset.card_le_card_of_injOn (fun l : Nat.Primes => (l : ℕ))
    · intro l hl
      have h1 := h l hl
      have h2 := l.2.one_lt
      simp only [Finset.coe_Icc, Set.mem_Icc, Finset.mem_Icc, Finset.mem_coe]
      omega
    · intro x _ y _ hxy
      exact Subtype.ext hxy
  simpa using key

/-- A single pointwise bound for nontrivial characters at the two exceptional primes
and for the remaining nontrivial resonant characters outside them. -/
def NontrivialCount : Prop :=
  HeightCounts.CountAt PChar.one fun h l _ _ e ψ =>
    ψ ≠ 1 ∧ (l ∈ Bchi h.chi ∨ (2 ≤ e ∧ l - 1 ∣ 2*e))

theorem exceptional_of_nontrivial_count (input : NontrivialCount) : HeightCounts.ExceptionalAt := by
  classical
  obtain ⟨C, bound⟩ := input
  refine ⟨2*C+2,?_⟩
  intro h one t ht big E _ _ _ field Ω _ _ _ ld S hS
  obtain ⟨Ω0, iF, iC, iA⟩ := exists_closure
  have hE : IsChiField h.chi h.ex h.q1 h.d E := one.symm ▸ field
  let M : ℝ := (h.N : ℝ) * t
  have hn : 16 ≤ h.N := Nat.le_of_dvd h.N_pos (hostIndex h).2.2.1
  have hM : 7 ≤ M := by
    have n : 16 ≤ (h.N:ℝ) := by exact_mod_cast hn
    have tt : 2 ≤ (t:ℝ) := by exact_mod_cast ht
    dsimp [M]
    nlinarith
  have hM0 : 0 ≤ M := by linarith
  have hpow : 0 ≤ M ^ (2*C) := pow_nonneg hM0 _
  haveI : NeZero h.N.totient := ⟨(Nat.totient_pos.2 h.N_pos).ne'⟩
  choose c hc using fun l : Nat.Primes => exists_coef (l : ℕ) h.N.totient
  have two (l : Nat.Primes) (hl : l ∈ S) : (l:ℕ) = 3 ∨ (l:ℕ) = 7 := by
    have hv := (hS l hl).2
    simpa only [exceptional_set, Finset.mem_insert, Finset.mem_singleton] using hv
  have small (l : Nat.Primes) (hl : l ∈ S) : (l:ℕ) ≤ 7 := by
    rcases two l hl with hl' | hl' <;> omega
  have each (l : Nat.Primes) (hl : l ∈ S) (e : ℕ) (he : 0 < e) (het : e < t)
      (ψ : DirichletCharacter (c l).O h.N) (mem : ψ ∈ h.X (c l) e) :
      VLe Ω0 (c l) e ψ (M^(2*C)) := by
    by_cases hψ : ψ = 1
    · subst ψ
      have hz : Vlen Ω0 (c l) e (1 : DirichletCharacter (c l).O h.N) = 0 := by
        obtain ⟨p,hp⟩ := l
        rcases two ⟨p,hp⟩ hl with h3 | h7
        · change p = 3 at h3
          subst p
          exact RegularCharacters.three Ω0 h _ _ he
        · change p = 7 at h7
          subst p
          exact RegularCharacters.seven Ω0 h _ _ he
      simp [VLe, Vn, Chr.nrm, hz, hpow]
    · have exceptional : (l:ℕ) ∈ Bchi h.chi := by simpa only [one] using (hS l hl).2
      have own := bound h one t big Ω0 l (c l) e (hS l hl).1 he het ψ mem ⟨hψ,Or.inl exceptional⟩
      apply VLe.mono Ω0 (c l) own
      have hlM : ((l:ℕ):ℝ) ≤ M := (by exact_mod_cast small l hl : ((l:ℕ):ℝ) ≤ 7).trans hM
      have heM : (h.N:ℝ)*e ≤ M := mul_le_mul_of_nonneg_left (by exact_mod_cast het.le) (by positivity)
      rw [pow_mul]
      apply pow_le_pow_left₀ (by positivity)
      rw [pow_two, mul_assoc]
      exact mul_le_mul hlM heM (by positivity) hM0
  have hfin : ∀ l ∈ S, ∀ e, 0 < e → e < t → ∀ ψ ∈ h.X (c l) e, Vlen Ω0 (c l) e ψ ≠ ⊤ :=
    fun l hl e he het ψ hm => (each l hl e he het ψ hm).1
  have hper : ∀ l ∈ S, (∀ e, 0 < e → e < t → plusLen (ld l) e ≠ ⊤) ∧
      ∑ e ∈ Finset.Ico 1 t, ((plusLen (ld l) e).toNat : ℝ) ≤
        ∑ e ∈ Finset.Ico 1 t, ∑ ψ ∈ h.X (c l) e, Vn Ω0 (c l) e ψ := by
    intro l hl
    haveI := (c l).dvr
    haveI := (c l).fin
    haveI := hc l
    have hidx := ExceptionalCharacters.odd_not_dvd_index h one l.2 (hS l hl).1
    have hlev := hostLevel h E hE
    have hT : ∀ e, (↑(h.X (c l) e) : Set (DirichletCharacter (↥(c l).O) h.N)) =
        Chr.evenSet (↥(c l).O) h.H e := by
      intro e
      ext ψ
      simp [Host.mem_X, Chr.evenSet, Host.IsChar, PsiEven]
    have hred := fun e (he : e ≠ 0) =>
      redPrime E h.N h.H hlev (l:ℕ) (hS l hl).1 hidx (c l) Ω (ld l) Ω0 e he (h.X (c l) e) (hT e)
    have r := Chr.sumBack (l:ℕ) (↥(c l).O) (DirichletCharacter (↥(c l).O) h.N)
      (fun e => if e < t then h.X (c l) e else ∅)
      ((Finset.range t).biUnion (fun e => h.X (c l) e))
      (fun ψ e => Vlen Ω0 (c l) e ψ) (fun e => plusLen (ld l) e) (fun _ => 0) t
      (by
        intro e
        split_ifs with h'
        · intro ψ hψ
          exact Finset.mem_biUnion.2 ⟨e, Finset.mem_range.2 h', hψ⟩
        · exact Finset.empty_subset _)
      (by
        intro e he1 he2
        simp only [he2, if_true, Nat.cast_zero, zero_mul, add_zero]
        exact ⟨hfin l hl e he1 he2, hred e he1.ne'⟩)
    refine ⟨r.1, ?_⟩
    have r2 := r.2
    simp only [Nat.cast_zero, Finset.sum_const_zero, mul_zero, add_zero] at r2
    refine r2.trans (le_of_eq (Finset.sum_congr rfl fun e he => ?_))
    simp only [Finset.mem_Ico] at he
    simp only [if_pos he.2]
    rfl
  refine ⟨fun l hl => (hper l hl).1,?_⟩
  have hcS : (S.card:ℝ) ≤ M := (by exact_mod_cast card_small S 7 small : (S.card:ℝ) ≤ 7).trans hM
  have per (l : Nat.Primes) (hl : l ∈ S) (e : ℕ) (he : e ∈ Finset.Ico 1 t) :
      Real.log (l:ℕ) * ∑ ψ ∈ h.X (c l) e, Vn Ω0 (c l) e ψ ≤ (h.N : ℝ) * M^(2*C) := by
    rw [Finset.mul_sum]
    calc _ ≤ ∑ ψ ∈ h.X (c l) e, M^(2*C) := by
           apply Finset.sum_le_sum
           intro ψ hmem
           rw [mul_comm]
           exact (each l hl e (Finset.mem_Ico.mp he).1 (Finset.mem_Ico.mp he).2 ψ hmem).2
         _ = ((h.X (c l) e).card:ℝ) * M^(2*C) := by rw [Finset.sum_const, nsmul_eq_mul]
         _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (xCard (↥(c l).O) h.N).1 _) hpow
  calc
    _ ≤ ∑ l ∈ S, M * M^(2*C) := by
      apply Finset.sum_le_sum
      intro l hl
      calc _ ≤ Real.log (l:ℕ) * ∑ e ∈ Finset.Ico 1 t, ∑ ψ ∈ h.X (c l) e, Vn Ω0 (c l) e ψ :=
             mul_le_mul_of_nonneg_left (hper l hl).2 (Real.log_nonneg (by exact_mod_cast l.2.one_lt.le))
           _ ≤ ∑ e ∈ Finset.Ico 1 t, (h.N : ℝ) * M^(2*C) := by
             rw [Finset.mul_sum]
             exact Finset.sum_le_sum (per l hl)
           _ ≤ (t:ℝ) * ((h.N:ℝ) * M^(2*C)) := by
             rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
             exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le t 1) (by positivity)
           _ = M * M^(2*C) := by dsimp [M]; ring
    _ = (S.card:ℝ) * (M * M^(2*C)) := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ M * (M * M^(2*C)) := mul_le_mul_of_nonneg_right hcS (mul_nonneg hM0 hpow)
    _ = M^(2*C+2) := by ring

/-- The two remaining estimates control the entire parity-adjusted plus height. -/
theorem height (generic : HeightCounts.CountIAt PChar.one)
    (nontrivial : NontrivialCount) : ConductorOneRH.Height := by
  apply HeightCounts.height_of_counts generic ?_ (exceptional_of_nontrivial_count nontrivial)
  obtain ⟨C, point⟩ := nontrivial
  refine ⟨C,?_⟩
  intro h one t big Ω _ _ _ l _ c e odd he ht ψ mem hψ
  exact point h one t big Ω l c e odd he ht ψ mem ⟨hψ.2.2.2,Or.inr ⟨hψ.2.1,hψ.2.2.1⟩⟩

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX in
theorem rh (weber : WeberBase.Weber) (generic : HeightCounts.CountIAt PChar.one)
    (nontrivial : NontrivialCount)
    (connect : HostExW (3/2) (GChi PChar.one).req → FamilyClassConnected ((GChi PChar.one).cls (3/2))) :
    RiemannHypothesis := ConductorOneRH.rh weber (height generic nontrivial) connect

end Principia.Ordinary.TwoCharacterCounts
end

#print axioms Principia.Ordinary.TwoCharacterCounts.exceptional_of_nontrivial_count
#print axioms Principia.Ordinary.TwoCharacterCounts.height
#print axioms Principia.Ordinary.TwoCharacterCounts.rh
