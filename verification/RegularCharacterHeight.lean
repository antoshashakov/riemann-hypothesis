import ConductorOneCases
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.TorsClass
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.GalOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ShaToShT
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PullOnto
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.PlacesQ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective

/-!
# Vanishing at a regular prime for the trivial character

This specialization was found through Principia's collaborative RH project.
The descent follows Levent Alpöge's quadratic-character calculation. Here
the full cyclotomic field kills the residual action, and its class number
kills the restricted cocycle. Inertia at the prime covers the quotient.
-/

namespace Principia.Ordinary.RegularCyclotomicBase
open NumberField NumberField.InfinitePlace IsCyclotomicExtension.Rat
open scoped Real

theorem three (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K] :
    classNumber K = 1 := classNumber_eq_one_iff.mpr (three_pid K)

theorem seven (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {7} ℚ K] :
    classNumber K = 1 := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hf : Module.finrank ℚ K = 6 := by rw [IsCyclotomicExtension.Rat.finrank 7 K]; decide
  have hc : nrComplexPlaces K = 3 := by rw [nrComplexPlaces_eq_totient_div_two 7]; decide
  have hdisc : discr K = -16807 := by rw [discr_prime 7 K]; norm_num
  let B : ℝ := (4/Real.pi)^nrComplexPlaces K *
    ((Module.finrank ℚ K).factorial/(Module.finrank ℚ K : ℝ)^(Module.finrank ℚ K) *
      Real.sqrt |(discr K : ℝ)|)
  have hB : B < 5 := by
    dsimp only [B]
    rw [hc,hf,hdisc]
    have hπ : 4/Real.pi ≤ (4/3 : ℝ) := by gcongr; exact Real.pi_gt_three.le
    have hs : Real.sqrt 16807 ≤ 130 := by
      rw [Real.sqrt_le_iff]; norm_num
    calc
      _ = (4/Real.pi)^3 * ((720:ℝ)/6^6*Real.sqrt 16807) := by norm_num [Nat.factorial]
      _ ≤ (4/3 : ℝ)^3 * ((720:ℝ)/6^6*130) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hπ 3)
          (mul_le_mul_of_nonneg_left hs (by positivity)) (by positivity) (by positivity)
      _ < _ := by norm_num
  have hb : ⌊B⌋₊ < 5 := (Nat.floor_lt' (by decide : 5 ≠ 0)).mpr (by simpa using hB)
  apply classNumber_eq_one_iff.mpr
  apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
  intro p hp hprime P hP hsize
  change p^P.inertiaDeg ℤ ≤ ⌊B⌋₊ at hsize
  have hp4 : p < 5 := lt_of_le_of_lt (Finset.mem_Icc.mp hp).2 hb
  have hp2 := hprime.two_le
  have pq : p = 2 ∨ p = 3 := by interval_cases p <;> norm_num at *
  letI : Fact p.Prime := ⟨hprime⟩
  letI : P.IsPrime := hP.1
  letI : P.LiesOver (Ideal.span {(p:ℤ)}) := hP.2
  have hn : ¬p ∣ 7 := by rcases pq with rfl|rfl <;> decide
  rw [inertiaDeg_eq_of_not_dvd (m:=7) p K P hn] at hsize
  exfalso
  rcases pq with rfl|rfl
  · norm_num only [Nat.cast_ofNat] at hsize
    have hh : orderOf (2:ZMod 7) ∣ 3 := orderOf_dvd_of_pow_eq_one (by decide)
    have hs := (Nat.dvd_prime Nat.prime_three).mp hh
    have hone : orderOf (2:ZMod 7) ≠ 1 := fun t => (by decide : (2:ZMod 7) ≠ 1) (orderOf_eq_one_iff.mp t)
    rw [hs.resolve_left hone] at hsize
    omega
  · norm_num only [Nat.cast_ofNat] at hsize
    have hh : orderOf (3:ZMod 7) ∣ 6 := orderOf_dvd_of_pow_eq_one (by decide)
    have hpos := Nat.pos_of_dvd_of_pos hh (by decide : 0<6)
    have hone : orderOf (3:ZMod 7) ≠ 1 := fun t => (by decide : (3:ZMod 7) ≠ 1) (orderOf_eq_one_iff.mp t)
    have he : 2 ≤ orderOf (3:ZMod 7) := by omega
    have h9 := Nat.pow_le_pow_right (by decide : 0<3) he
    omega

end Principia.Ordinary.RegularCyclotomicBase

noncomputable section
namespace Principia.Ordinary.RegularCharacters

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.ML UpperTheory.V.X

private theorem zq_unit {l : ℕ} [Fact l.Prime] (x : ℤ_[l]) (h : PadicInt.toZMod x ≠ 0) : IsUnit x := by
  by_contra hx
  apply h
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod]
  exact hx

private theorem zq_dvd {l : ℕ} [Fact l.Prime] (x : ℤ_[l]) (h : PadicInt.toZMod x = 0) : (l : ℤ_[l]) ∣ x := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h
  exact h

private theorem zq_gen {l e : ℕ} [Fact l.Prime] (h2 : ¬ l - 1 ∣ e) :
    ∃ u : ℤ_[l]ˣ, PadicInt.toZMod (u : ℤ_[l]) ^ e ≠ 1 := by
  obtain ⟨b, hb⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  have ho : orderOf b = l - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hb, Nat.card_eq_fintype_card, ZMod.card_units]
  have h0 : PadicInt.toZMod (((b : ZMod l).val : ℕ) : ℤ_[l]) = b := by
    rw [map_natCast, ZMod.natCast_zmod_val]
  obtain ⟨u, hu⟩ := zq_unit _ (h0 ▸ b.ne_zero)
  refine ⟨u, fun h => h2 ?_⟩
  rw [hu, h0] at h
  rw [← ho, orderOf_dvd_iff_pow_eq_one]
  exact Units.ext (by simpa using h)

private theorem regular_hom (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K]
    [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ) (hp : l.Prime) (regular : l.Coprime (classNumber K))
    (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (h2 : ∀ m : M, 2 • m = 0 → m = 0)
    (φ : galOf ℚ K Ω → M) (hφ : φ ∈ Kum.XDual l (galOf ℚ K Ω) R M) (u : galOf ℚ K Ω) (hu : l • φ u = 0) : φ u = 0 := by
  rw [← Kum.pullOnto ℚ Ω K _ le_rfl l R M hp.ne_zero le_rfl (Or.inr h2)] at hφ
  obtain ⟨θ, hθ, rfl⟩ := hφ
  rw [Kum.clPull_apply] at hu ⊢
  generalize Kum.artCl K Ω (Kum.toGal K le_rfl u) = c at hu ⊢
  let θ' : ClassGroup (𝓞 K) →* Multiplicative M := MonoidHom.mk' (fun c => Multiplicative.ofAdd (θ c)) fun a b => by
    rw [hθ.1, ofAdd_add]
  have h1 : classNumber K • θ c = 0 := by
    have : θ' (c ^ classNumber K) = 1 := by rw [classNumber, pow_card_eq_one, map_one]
    rw [map_pow] at this
    exact this
  have := Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hu) (addOrderOf_dvd_of_nsmul_eq_zero h1)
  rw [regular.gcd_eq_one, Nat.dvd_one, AddMonoid.addOrderOf_eq_one_iff] at this
  exact this

/-- If the cyclotomic field of prime conductor has class number prime to ℓ,
the trivial-character cohomology vanishes for every positive twist. -/
theorem trivial_of_regular (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    (l : ℕ) [hp : Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (odd : l ≠ 2)
    (regular : ∀ (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {l} ℚ K], l.Coprime (classNumber K))
    (e : ℕ) (positive : 1 ≤ e) : Chr.V l e (1 : G ℚ Ω →* Oˣ) = 0 := by
  classical
  by_cases h2 : l - 1 ∣ e
  · exact UpperTheory.V.X.zOne Ω l O odd e positive h2
  have hl : 3 ≤ l := by have := hp.out.two_le; omega
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  letI : NeZero l := ⟨hp.out.ne_zero⟩
  obtain ⟨w, hw⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  let K := IntermediateField.adjoin ℚ {w}
  letI : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral w)
  letI : NumberField K := NumberField.of_module_finite ℚ _
  letI hk : IsCyclotomicExtension {l} ℚ K := hw.intermediateField_adjoin_isCyclotomicExtension ℚ
  letI : IsCyclotomicExtension {l^1} ℚ K := by simpa only [pow_one] using hk
  have hU (g : G ℚ Ω) : g ∈ galOf ℚ K Ω ↔ PadicInt.toZModPow 1 (cycZ ℚ Ω l g : ℤ_[l]) = 1 := by
    rw [Kum.galOfCyc ℚ Ω l 1 ℚ K]
    have hQ : g ∈ galOf ℚ ℚ Ω := fun x => g.commutes x
    simp only [levU, Subgroup.mem_inf, hQ, true_and, Subgroup.mem_comap,
      KStar.TotallyRealRoots.princ, MonoidHom.mem_ker, KStar.TotallyRealRoots.redPow,
      Units.ext_iff, Units.coe_map, MonoidHom.coe_coe, Units.val_one]
    rfl
  have hpow (g : G ℚ Ω) (hg : g ∈ galOf ℚ K Ω) :
      PadicInt.toZMod (cycZ ℚ Ω l g : ℤ_[l]) ^ e = 1 := by
    have hd : PadicInt.toZModPow 1 ((cycZ ℚ Ω l g : ℤ_[l]) - 1) = 0 := by
      rw [map_sub, (hU g).mp hg, map_one, sub_self]
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, pow_one, ← PadicInt.maximalIdeal_eq_span_p,
      ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hd
    rw [hd,one_pow]
  obtain ⟨u, hu⟩ := zq_gen h2
  obtain ⟨A₀, hA₀⟩ := (B3.placesQ Ω).1 l hp.out
  obtain ⟨δ, hδI, hδ⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A₀ hA₀ u
  set α : G ℚ Ω →* Oˣ := (1 : G ℚ Ω →* Oˣ)⁻¹ * chiO ℚ Ω l O ^ (-(e : ℤ)) with hα
  have hαg : ∀ g, α g = Units.map (algebraMap ℤ_[l] O).toMonoidHom (cycZ ℚ Ω l g ^ e)⁻¹ := fun g => by
    simp [hα, chiO]
  have hαs : ∀ g, (α g : O) - 1 = algebraMap ℤ_[l] O (-((cycZ ℚ Ω l g ^ e)⁻¹ : ℤ_[l]ˣ) * ((cycZ ℚ Ω l g : ℤ_[l]) ^ e - 1)) :=
    fun g => by
      rw [hαg, ← Units.val_pow_eq_pow_val, mul_sub, neg_mul, Units.inv_mul, map_sub]
      simp [sub_eq_neg_add, add_comm]
  have hun : ∀ g, cycZ ℚ Ω l g = u → IsUnit ((α g : O) - 1) := fun g hg => by
    rw [hαs, hg]
    refine IsUnit.map _ ((Units.isUnit _).neg.mul (zq_unit _ ?_))
    rw [map_sub, map_pow, map_one]
    exact sub_ne_zero.2 hu
  have htr : ∀ g : G ℚ Ω, g ∈ galOf ℚ K Ω → ∀ m : QO l O, l • m = 0 → (α g : O) • m = m := fun g hg m hm => by
    obtain ⟨y, hy⟩ := zq_dvd ((cycZ ℚ Ω l g : ℤ_[l]) ^ e - 1) (by rw [map_sub, map_pow, map_one, hpow g hg, sub_self])
    have : ((α g : O) - 1) • m = 0 := by
      rw [hαs, hy, mul_left_comm, map_mul, map_natCast, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul, hm, smul_zero]
    rwa [sub_smul, one_smul, sub_eq_zero] at this
  have hin : ∀ A : ValuationSubring Ω, ¬ Over A l → ∀ g ∈ Ine (F := ℚ) A, α g = 1 := fun A hA g hg => by
    have : cycZ ℚ Ω l g = 1 := (places ℚ Ω l A).2.2.2 hA hg
    rw [hαg, this, one_pow, inv_one, map_one]
  have htwo : ∀ m : QO l O, 2 • m = 0 → m = 0 := fun m hm => by
    have h : IsUnit ((2 : ℕ) : O) := by
      rw [← map_natCast (algebraMap ℤ_[l] O)]
      refine IsUnit.map _ (zq_unit _ ?_)
      rw [map_natCast, Ne, ZMod.natCast_eq_zero_iff]
      exact fun h => absurd (Nat.le_of_dvd two_pos h) (by omega)
    exact h.smul_eq_zero.1 ((Nat.cast_smul_eq_nsmul _ _ _).trans hm)
  have key : ∀ a : O, ∀ c ∈ ShT (QO l O) α δ l a, l • c = 0 → c = 0 := by
    rintro a c ⟨⟨hlc, hc⟩, hcδ, -, hI, hD⟩ hcl
    have hcl' : ∀ g, l • c g = 0 := fun g => congrFun hcl g
    have hdec : ∀ A : ValuationSubring Ω, Over A l → ∀ g ∈ Dec (F := ℚ) A, g ∈ galOf ℚ K Ω → c g = 0 := fun A hA g hg hgs => by
      obtain ⟨m, -, hm⟩ := hD A hA
      obtain ⟨t, ht, htu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA u
      have hlm : l • m = 0 := by
        refine (hun t htu).smul_eq_zero.1 ?_
        rw [smul_comm, sub_smul, one_smul, ← hm t (Ine_le_Dec (F := ℚ) A ht), hcl']
      rw [hm g hg, htr g hgs m hlm, sub_self]
    have hX : (fun v : galOf ℚ K Ω => c v) ∈ Kum.XDual l (galOf ℚ K Ω) O (QO l O) := by
      refine ⟨hlc.comp_continuous continuous_subtype_val, fun v w => ?_, fun A v hv => ?_, fun A hA v hv => ?_⟩
      · show c (v * w) = c v + c w
        rw [hc, htr v v.2 _ (hcl' _)]
      · by_cases hA : Over A l
        · exact hdec A hA v (Ine_le_Dec (F := ℚ) A hv) v.2
        · exact hI A hA v hv
      · exact hdec A hA v hv v.2
    have h0 : ∀ g : G ℚ Ω, g ∈ galOf ℚ K Ω → c g = 0 := fun g hg =>
      regular_hom Ω K l hp.out (regular K) O (QO l O) htwo _ hX ⟨g,hg⟩ (hcl' g)
    have local_zero : ∀ t ∈ Dec (F := ℚ) A₀, c t = 0 := by
      obtain ⟨m, -, hm⟩ := hD A₀ hA₀
      have hz : ((α δ : O) - 1) • m = 0 := by
        rw [sub_smul, one_smul, ← hm δ (Ine_le_Dec (F := ℚ) A₀ hδI), hcδ]
      have hm0 := (hun δ hδ).smul_eq_zero.mp hz
      intro t ht
      rw [hm t ht, hm0, smul_zero, sub_self]
    funext g
    obtain ⟨t, ht, htg⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A₀ hA₀ (cycZ ℚ Ω l g)
    have hk : t⁻¹ * g ∈ galOf ℚ K Ω := (hU _).mpr (by simp [map_mul,map_inv,htg])
    rw [← mul_inv_cancel_left t g, hc, local_zero t (Ine_le_Dec (F := ℚ) A₀ ht),
      h0 _ hk, smul_zero, add_zero, Pi.zero_apply]
  refine nonpos_iff_eq_zero.1 (shaToShT Ω l O α δ (hun δ hδ) l hp.out.ne_zero hin (fun A h h' => absurd h h') 0 fun a ha => ?_)
  have hnu : ¬ IsUnit (l : O) := fun h => by
    haveI := (dvrFacts l O).2.2.1
    rw [← map_natCast (algebraMap ℤ_[l] O), isUnit_map_iff] at h
    exact PadicInt.irreducible_p.not_isUnit h
  obtain ⟨n, hn⟩ : ∃ n : ℕ, a ∣ (l : O) ^ n := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hπ
    refine ⟨n, hn.dvd.trans (pow_dvd_pow_of_dvd ?_ n)⟩
    rw [← Ideal.mem_span_singleton, ← hπ.maximalIdeal_eq]
    exact hnu
  have hall : ∀ n : ℕ, ∀ c ∈ ShT (QO l O) α δ l a, l ^ n • c = 0 → c = 0 := by
    intro n
    induction n with
    | zero => intro c _ h; simpa using h
    | succ n ih =>
      intro c hc h
      exact ih c hc (key a _ (nsmul_mem hc _) (by rw [smul_smul, ← pow_succ', h]))
  have : ShT (QO l O) α δ l a = ⊥ := by
    refine eq_bot_iff.2 fun c hc => hall n c hc (funext fun g => ?_)
    obtain ⟨y, hy⟩ := hn
    rw [Pi.smul_apply, ← Nat.cast_smul_eq_nsmul O, Nat.cast_pow, hy, mul_comm, mul_smul, hc.2.2.1 g, smul_zero, Pi.zero_apply]
  rw [this]
  simp

local instance : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

/-- The bound at 3 holds for every positive twist and host level. -/
theorem three (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    (h : UpperTheory.V.HV.Host) (c : UpperTheory.V.HV.Coef 3) (e : ℕ) (he : 1 ≤ e) :
    UpperTheory.V.HV.Vlen Ω c e (1 : DirichletCharacter c.O h.N) = 0 := by
  have hd : Chr.dirG ℚ Ω (1 : DirichletCharacter c.O h.N) = 1 := by
    ext σ
    simp [Chr.dirG]
  unfold UpperTheory.V.HV.Vlen
  rw [hd]
  apply le_antisymm ((Chr.V'_le_V 3 h.N e 1).trans ?_) bot_le
  apply (trivial_of_regular Ω 3 c.O (by decide) ?_ e he).le
  intro K _ _ _
  rw [RegularCyclotomicBase.three K]
  exact Nat.coprime_one_right _

/-- The bound at 7 holds for every positive twist and host level. -/
theorem seven (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    (h : UpperTheory.V.HV.Host) (c : UpperTheory.V.HV.Coef 7) (e : ℕ) (he : 1 ≤ e) :
    UpperTheory.V.HV.Vlen Ω c e (1 : DirichletCharacter c.O h.N) = 0 := by
  have hd : Chr.dirG ℚ Ω (1 : DirichletCharacter c.O h.N) = 1 := by
    ext σ
    simp [Chr.dirG]
  unfold UpperTheory.V.HV.Vlen
  rw [hd]
  apply le_antisymm ((Chr.V'_le_V 7 h.N e 1).trans ?_) bot_le
  apply (trivial_of_regular Ω 7 c.O (by decide) ?_ e he).le
  intro K _ _ _
  rw [RegularCyclotomicBase.seven K]
  exact Nat.coprime_one_right _

end Principia.Ordinary.RegularCharacters
end

#print axioms Principia.Ordinary.RegularCharacters.trivial_of_regular
#print axioms Principia.Ordinary.RegularCharacters.three
#print axioms Principia.Ordinary.RegularCharacters.seven
