import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PoitouTateDualityOfNormalised
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ABoundOfIsTower
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.AdmissibleOfPageN
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Kmono
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.PartA
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Window
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.BOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.ExpStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.ExponentLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.FProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.NumThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.PiRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.RingEquivalences.OrderOfOneAddPrimePowZmodPrimePow
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SClassOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SFinal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SThetaOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.STrans
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SUpperOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ThmBcOfPsiBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Iv
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IsAlgClosureRat
import Development.AutomorphicArithmetic.CharacterBoxes.SupplyChi
import Development.AutomorphicArithmetic.CharacterBoxes.ZeroFreeAllOfTopG
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.UnramifiedOrthogonality
import Development.EtaleCohomology.CyclotomicDiscriminants.FinSDetect
import Development.EtaleCohomology.CyclotomicDiscriminants.FinSFewOf
import Development.EtaleCohomology.CyclotomicDiscriminants.FinSLayer
import Development.EtaleCohomology.CyclotomicDiscriminants.FinSRel
import Development.EtaleCohomology.CyclotomicDiscriminants.FinSStein
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PoitouTateNineTerm.PoitouTateNormalisedHolds
import Formalism.GammaFactorNonvanishing.RhOfRight

/-!
# Ordinary RH from a cubic-log height bound and a principal family

This reduction was found through Principia's collaborative Riemann Hypothesis project,
specializing Levent Alpöge's proof. At a host of modulus N and height t,
`ConductorOneRH.LogCubeHeight` allows a bound of exp(C (1 + log(Nt))³).
The geometric family hypothesis is stated in `ConductorOneRH.rh_of_logCube`. The argument uses
Alpöge's odd-prime minus bound, high-twist counts and connected-family comparison.
-/

noncomputable section

namespace Principia.Ordinary.Growth
open Filter
theorem cube_absorbed {ε A : ℝ} (he : 0 < ε) (hA : 0 ≤ A) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ u : ℝ, 1 ≤ u → Real.log u ≤ 2 * x^(ε/4) →
      Real.exp (A * (1 + Real.log u)^3) ≤ Real.exp (x^(4*ε/5)) := by
  obtain ⟨x₀,large⟩ := eventually_atTop.1
    ((tendsto_rpow_atTop (by positivity : 0 < ε/20)).eventually_ge_atTop (27*A))
  refine ⟨max 1 x₀, ?_⟩
  intro x hx u hu hu'
  have hx₁ : 1 ≤ x := (le_max_left _ _).trans hx
  have hx₀ : 0 < x := by linarith
  let a := x^(ε/4)
  have ha : 1 ≤ a := Real.one_le_rpow hx₁ (by positivity)
  have hp : (1 + Real.log u)^3 ≤ (3*a)^3 :=
    pow_le_pow_left₀ (by linarith [Real.log_nonneg hu]) (by change Real.log u ≤ 2*a at hu'; linarith) 3
  have split : a^3 * x^(ε/20) = x^(4*ε/5) := by
    dsimp [a]
    rw [← Real.rpow_natCast (x^(ε/4)) 3, ← Real.rpow_mul hx₀.le, ← Real.rpow_add hx₀]
    congr 1
    push_cast
    ring
  apply Real.exp_le_exp.mpr
  calc A * (1 + Real.log u)^3 ≤ A * (3*a)^3 := mul_le_mul_of_nonneg_left hp hA
    _ = a^3 * (27*A) := by ring
    _ ≤ a^3 * x^(ε/20) := mul_le_mul_of_nonneg_left
      (large x ((le_max_right _ _).trans hx)) (by positivity)
    _ = x^(4*ε/5) := split
end Principia.Ordinary.Growth

namespace Principia.Ordinary.Growth
theorem power_le_logCube {u : ℝ} (hu : 1 ≤ u) (C : ℕ) :
    u^C ≤ Real.exp ((C:ℝ) * (1 + Real.log u)^3) := by
  have up : 0 < u := by linarith
  have hl : 0 ≤ Real.log u := Real.log_nonneg hu
  have hl' : Real.log u ≤ (1 + Real.log u)^3 := by
    nlinarith [sq_nonneg (Real.log u), pow_nonneg hl 3]
  have hc := mul_le_mul_of_nonneg_left hl' (Nat.cast_nonneg (α:=ℝ) C)
  rw [← Real.rpow_natCast u C, Real.rpow_def_of_pos up]
  exact Real.exp_le_exp.mpr (by linarith)
end Principia.Ordinary.Growth

namespace Principia.Ordinary.WeberBase

open NumberField Formalism.HC UpperTheory.Top UpperTheory.V UpperTheory.V.Two

def Weber : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (F : Type) [Field F] [NumberField F]
    [IsCyclotomicExtension {2^n} ℚ F], Odd (classNumber F)

theorem with_i : withI (AbF.ofChar PChar.one) = AbF.cyc 4 := by
  change (⟨4,by decide, _⟩ : AbF) = ⟨4,by decide,⊥⟩
  congr 1
  have hm (x : (ZMod 4)ˣ) : ZMod.unitsMap (dvd_refl 4) x = x := by
    apply Units.ext
    simp <;> rfl
  apply Subgroup.ext
  intro x
  change ((ZMod.unitsMap (by decide : 1 ∣ 4) x ∈ (AbF.ofChar PChar.one).H) ∧
    ZMod.unitsMap (dvd_refl 4) x = 1) ↔ x = 1
  refine ⟨fun h => (hm x).symm.trans h.2,?_⟩
  rintro rfl
  exact ⟨(ZMod.unitsMap (by decide : 1 ∣ 4)).map_one ▸ (AbF.ofChar PChar.one).H.one_mem,
    (ZMod.unitsMap (dvd_refl 4)).map_one⟩

theorem realized : IsAbField (withI (AbF.ofChar PChar.one)) (CyclotomicField 4 ℚ) := by
  rw [with_i]
  let K := CyclotomicField 4 ℚ
  letI : IsCyclotomicExtension {4} ℚ K := CyclotomicField.isCyclotomicExtension 4 ℚ
  let z := IsCyclotomicExtension.zeta 4 ℚ K
  have hz : IsPrimitiveRoot z 4 := IsCyclotomicExtension.zeta_spec 4 ℚ K
  refine ⟨4,inferInstance,AlgHom.id ℚ K,z,by decide,hz,fun σ a hσ => ?_⟩
  have ker : (AbF.cyc 4).ker a ↔ a ≡ 1 [MOD 4] := by
    change (∃ u : (ZMod 4)ˣ, u ∈ (⊥ : Subgroup _) ∧ (u : ZMod 4) = a) ↔ _
    rw [← ZMod.natCast_eq_natCast_iff]
    simp [eq_comm]
  rw [ker]
  have hh : σ z = z ↔ a ≡ 1 [MOD 4] := by
    rw [hσ]
    have ho : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.mpr ⟨4,by decide,hz.pow_eq_one⟩
    simpa only [pow_one,←hz.eq_orderOf] using ho.pow_eq_pow_iff_modEq (n:=a) (m:=1)
  rw [←hh]
  refine ⟨fun h => h z,fun h => ?_⟩
  have hσ' : σ = (AlgEquiv.refl : K ≃ₐ[ℚ] K) :=
    IsCyclotomicExtension.algEquiv_eq_of_apply_eq {4} ℚ K fun m hm _ => by
      obtain rfl := Set.mem_singleton_iff.mp hm
      exact ⟨z,hz,h⟩
  simp [hσ']

theorem squares_surjective (G : Type*) [CommGroup G] [Finite G] (h : Odd (Nat.card G)) :
    Function.Surjective (powMonoidHom 2 : G →* G) := by
  obtain ⟨k,hk⟩ := h
  intro a
  refine ⟨a^(k+1),?_⟩
  change (a^(k+1))^2 = a
  rw [←pow_mul,show (k+1)*2 = Nat.card G+1 by omega,pow_succ,pow_card_eq_one',one_mul]

theorem class_quotient (web : Weber) (n : ℕ) (hn : 2 ≤ n)
    (K F : Type) [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]
    [Field F] [NumberField F] [Algebra K F] [IsScalarTower ℚ K F]
    [IsCyclotomicExtension {2^n} K F] :
    Nat.card (ClassGroup (𝓞 F) ⧸ (powMonoidHom 2 : ClassGroup (𝓞 F) →* _).range) = 1 := by
  have hu := IsCyclotomicExtension.trans ({4}:Set ℕ) {2^n} ℚ K F (algebraMap K F).injective
  have hd : 4 ∣ 2^n := (by norm_num : (4:ℕ) ∣ 2^2).trans (pow_dvd_pow 2 hn)
  letI : IsCyclotomicExtension {2^n} ℚ F :=
    (IsCyclotomicExtension.iff_union_of_dvd ℚ F (S:=({2^n}:Set ℕ)) (n:=4)
      ⟨2^n,rfl,by positivity,hd⟩).mpr (by simpa only [Set.union_comm] using hu)
  have odd : Odd (Nat.card (ClassGroup (𝓞 F))) := by
    simpa only [classNumber,Nat.card_eq_fintype_card] using web n hn F
  change (powMonoidHom 2 : ClassGroup (𝓞 F) →* _).range.index = 1
  exact Subgroup.index_eq_one.mpr (MonoidHom.range_eq_top.mpr (squares_surjective _ odd))

end Principia.Ordinary.WeberBase

namespace Principia.Ordinary.WeberRank

open NumberField Formalism.HC Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two

private theorem fn_cyclotomic (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (n : ℕ) : IsCyclotomicExtension {2^n} K (Fn K Ω 2 n) :=
  (fnCyc K Ω 2 n).1

theorem gaussian (web : Principia.Ordinary.WeberBase.Weber) (Ω : Type) [Field Ω]
    [Algebra (CyclotomicField 4 ℚ) Ω] [IsAlgClosure (CyclotomicField 4 ℚ) Ω] :
    XRk 2 1 (cycU 2 (⊤ : Subgroup (G (CyclotomicField 4 ℚ) Ω))) 0 := by
  let K := CyclotomicField 4 ℚ
  letI : IsCyclotomicExtension {4} ℚ K := CyclotomicField.isCyclotomicExtension 4 ℚ
  apply infRk K Ω 2 1 0 ⊤ one_ne_zero isClosed_univ
  intro n hn
  let F := Fn K Ω 2 n
  letI : IsCyclotomicExtension {2^n} K F := fn_cyclotomic K Ω n
  letI : IsScalarTower ℚ K F := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  exact levelRk K Ω 2 n 0 hn (by simpa only [pow_zero] using
    (Principia.Ordinary.WeberBase.class_quotient web n hn K F).le)

theorem base_zero (web : Principia.Ordinary.WeberBase.Weber) (Ω : Type) [Field Ω]
    [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] :
    XRk 2 1 (cycU 2 (abU Ω (withI (AbF.ofChar PChar.one)))) 0 := by
  let K := CyclotomicField 4 ℚ
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  letI : Algebra K Ω := (IsAlgClosed.lift : K →ₐ[ℚ] Ω).toRingHom.toAlgebra
  letI : IsScalarTower ℚ K Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : IsAlgClosure K Ω := ⟨inferInstance,Algebra.IsAlgebraic.tower_top (K:=ℚ) K⟩
  rw [←abField Ω _ K Principia.Ordinary.WeberBase.realized]
  exact (rkTransport ℚ Ω K 2 1 0).mp (gaussian web Ω)

theorem moving_rank (web : Principia.Ordinary.WeberBase.Weber) (Ω : Type) [Field Ω]
    [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (q d : ℕ) (hp : PrimePair 1 q d) :
    XRk 2 1 (cycU 2 (abU Ω (base2 (AbF.ofChar PChar.one) q d))) 24 := by
  have hdeg : (AbF.ofChar PChar.one).deg = 1 := by
    change (1 : DirichletCharacter ℂ 1).toUnitHom.ker.index = 1
    exact Subgroup.index_eq_one.mpr (Subsingleton.elim _ _)
  simpa only [hdeg,zero_add,Nat.mul_one] using
    baseRk Ω (AbF.ofChar PChar.one) q d 0 hp (base_zero web Ω)

end Principia.Ordinary.WeberRank

namespace Principia.Ordinary.WeberTower

open NumberField Formalism.HC Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two

theorem tower (web : Principia.Ordinary.WeberBase.Weber) (q d : ℕ) (pair : PrimePair 1 q d)
    (L : Type) [Field L] [NumberField L] (realized : IsAbField (base2 (AbF.ofChar PChar.one) q d) L) :
    Tower.GenLE ℤ_[2] (Tower.XX 2 L) 24 ∧ Tower.IsTower 2 L 24 := by
  haveI := isAlgClosure_rat L (AlgebraicClosure L)
  have rank := Principia.Ordinary.WeberRank.moving_rank web (AlgebraicClosure L) q d pair
  have mu := hasMuQ.2.2 _ q d L realized
  exact ⟨genLE_of_abRk 1 L realized rank,complex_of_root (by norm_num) mu,mu,by decide,
    genLE_of_abRk 2 L realized rank⟩

end Principia.Ordinary.WeberTower

namespace Principia.Ordinary.TwistCohomologyBound

open Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.ZK

theorem exists_exponent (pt : GlobalTheory.Published.PoitouTateDuality)
    (lf : LocalFinitenessK) (ltate : LocalTateDualityK) : ∃ C, LemmaK C :=
  lemmaK_of_steps bOdd pt lf ltate sChain sPrism sPrismMul sZc
    LateralTheory.Fin.SRel.intersectionNumber_baseChange sTrans sCoc sThetaOf sPhi sEta
    LateralTheory.Fin.SStein.intersectionNumber_baseChange sClassOf sUpperOf
    LateralTheory.Fin.SDetect.intersectionNumber_baseChange sCount
    LateralTheory.Fin.SFewOf.intersectionNumber_baseChange PositivityTheory.QuaternionShaBounds.sSha
    LateralTheory.Fin.SLayer.intersectionNumber_baseChange sTors sNum sFinal

end Principia.Ordinary.TwistCohomologyBound

namespace Principia.Ordinary.ClassicalWindowRH

open UpperTheory.Top UpperTheory.V.HV
open CompanionTheory.LocalTateOrthogonality.Gcoh

theorem duality : GlobalTheory.Published.PoitouTateDuality :=
  GlobalTheory.PoitouTateConj.poitouTateDuality_of_normalised
    PositivityTheory.Lit1.PTN.poitouTateNormalised_holds

end Principia.Ordinary.ClassicalWindowRH

namespace Principia.Ordinary.PrincipalPrimes

open NumberField Formalism.HC UpperTheory.V

theorem degree_one : (AbF.ofChar PChar.one).deg = 1 := by
  change (1 : DirichletCharacter ℂ 1).toUnitHom.ker.index = 1
  apply Subgroup.index_eq_one.mpr
  exact Subsingleton.elim _ _

theorem minus_estimate (C : ℝ) (n N t : ℕ) :
    minusBound C (AbF.ofChar PChar.one).deg n N t =
      3*n*(t:ℝ)^2*Real.log ((t:ℝ)*N) := by
  simp [minusBound,degree_one]

end Principia.Ordinary.PrincipalPrimes

namespace Principia.Ordinary.PrincipalBudget

open NumberField Formalism.HC UpperTheory.Top UpperTheory.V UpperTheory.V.HV

def HostBudget : Prop :=
    ∃ C r₁ r₂ : ℕ, r₁.Prime ∧ r₂.Prime ∧ ∀ h : Host, h.chi = PChar.one →
      r₁ < h.q1 → r₁ < h.d → r₂ < h.q1 → r₂ < h.d → ∀ t : ℕ, 2 ≤ t → h.Big t →
      ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
        IsChiField PChar.one h.ex h.q1 h.d E → ∀ B₂ : ℝ, VVat 2 E t B₂ →
        VVle E t (B₂*Real.log 2 +
          3*(Module.finrank ℚ E:ℝ)*(t:ℝ)^2*Real.log ((t:ℝ)*condF E) + Real.exp ((C:ℝ) * (1 + Real.log ((h.N:ℝ)*t))^3))

end Principia.Ordinary.PrincipalBudget

namespace Principia.Ordinary.DyadicTransfer

open NumberField Formalism.HC UpperTheory.Top UpperTheory.V UpperTheory.V.HV

def AtScale (eps Ct : ℝ) : Prop :=
    ∃ (r₁ r₂ : ℕ) (x₀ : ℝ), r₁.Prime ∧ r₂.Prime ∧ ∀ x ≥ x₀,
      ∀ h : Host, h.chi = PChar.one → r₁ < h.q1 → r₁ < h.d → r₂ < h.q1 → r₂ < h.d →
      2 ≤ ⌊x^Ct⌋₊ → h.Big ⌊x^Ct⌋₊ → PageN eps x h.ex →
      Real.log ((h.q1:ℝ)*h.d) ≤ x^(eps/4) →
      BaAt (AbF.ofChar PChar.one) eps (fun _ => h.ex) (fun y => ⌊y^Ct⌋₊) h.q1 h.d x →
      VAt PChar.one eps Ct h.q1 h.d h.ex x

theorem from_budget (budget : Principia.Ordinary.PrincipalBudget.HostBudget)
    (eps Ct : ℝ) (heps : 0 < eps) (htiny : eps < 1/52) : AtScale eps Ct := by
  obtain ⟨C,r₁,r₂,h₁,h₂,H⟩ := budget
  obtain ⟨K,hK,hm⟩ := minusBound_le_exp_of_log_le 0 1
  obtain ⟨x₁,he⟩ := error_terms_le_sqrt_exp_rpow eps K 1 heps
  obtain ⟨x₃,cube⟩ := Growth.cube_absorbed (A := (C:ℝ)) heps (Nat.cast_nonneg C)
  obtain ⟨x₂,hl⟩ := log_conductor_mul_height_le_of_pageN eps Ct 1 heps htiny
  refine ⟨r₁,r₂,max 1 (max x₁ (max x₂ x₃)),h₁,h₂,?_⟩
  intro x hx h heq hrq hrd hsq hsd ht hbig hpage hlog hdy E _ _ hE
  let t := ⌊x^Ct⌋₊
  have hx₁ : x₁ ≤ x := le_trans (le_max_left _ _) ((le_max_right _ _).trans hx)
  have hx₂₃ : max x₂ x₃ ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hx₂ : x₂ ≤ x := (le_max_left _ _).trans hx₂₃
  have hx₃ : x₃ ≤ x := (le_max_right _ _).trans hx₂₃
  have hxpos : 0 ≤ x := le_trans (by norm_num : (0:ℝ)≤1) ((le_max_left _ _).trans hx)
  have ht₁ : 1 ≤ t := le_trans (by decide : 1 ≤ 2) ht
  have htX : (t:ℝ) ≤ x^Ct := Nat.floor_le (Real.rpow_nonneg hxpos _)
  have hq := h.pair.1
  have hd := h.pair.2.2.1
  have hq4 : h.q1%4=3 := by have hq8 := h.pair.2.1; omega
  letI : IsCMField E := isCMField_of_isChiField _ _ _ _ hq hq4 E hE
  have hN : h.N = 2^(h.ex+2)*1*h.q1*h.d := by
    simp [Host.N,Host.q,heq,PChar.one,Nat.mul_assoc]
  have hNpos : 1 ≤ h.N := h.N_pos
  have hNH := hl x hx₂ h.N t h.ex h.q1 h.d hNpos hN.le hpage ht₁ htX hlog
  obtain ⟨hfpos,hfle,hdeg⟩ := conductor_bounds_of_isChiField PChar.one h.ex h.q1 h.d
    hq.pos hd.pos E hE
  have hFH := hl x hx₂ (condF E) t h.ex h.q1 h.d hfpos hfle hpage ht₁ htX hlog
  have hmin := hm (Module.finrank ℚ E) (condF E) t (x^(eps/4)) hfpos ht₁ hdeg hFH
  have hid : minusBound 0 1 (Module.finrank ℚ E) (condF E) t =
      3*(Module.finrank ℚ E:ℝ)*(t:ℝ)^2*Real.log ((t:ℝ)*condF E) := by
    simpa only [Principia.Ordinary.PrincipalPrimes.degree_one] using
      Principia.Ordinary.PrincipalPrimes.minus_estimate 0 (Module.finrank ℚ E) (condF E) t
  rw [hid] at hmin
  have hnu : 1 ≤ (h.N:ℝ)*t := one_le_mul_of_one_le_of_one_le (by exact_mod_cast hNpos) (by exact_mod_cast ht₁)
  have hbudget := he x hx₁ ((h.N:ℝ)*t) hnu hNH
  simp only [Real.rpow_one, one_mul] at hbudget
  have hcubic := cube x hx₃ ((h.N:ℝ)*t) hnu hNH
  have htwo := hdy E ((isCompField_ofChar _ _ _ _ _).mpr hE)
  have htotal := H h heq hrq hrd hsq hsd t ht hbig E hE _ htwo
  apply htotal.mono le_rfl
  linarith

end Principia.Ordinary.DyadicTransfer

namespace Principia.Ordinary.DyadicWindows

open NumberField Formalism.HC UpperTheory.Top UpperTheory.V UpperTheory.V.HV

def WindowAt (J eps : ℝ) (condition : ℕ → ℕ → ℝ → Prop) : Prop :=
  ∃ X₀ : ℝ, ∀ X ≥ X₀, ∀ q d : ℕ, WinPair eps (X^(1/J)) q d →
    ∃ Y : ℝ, X^(1/J) ≤ Y ∧ Y^(2:ℝ) ≤ X ∧
      ∀ x : ℝ, Y ≤ x → x ≤ Y^(2:ℝ) → condition q d x

theorem at_index (budget : Principia.Ordinary.PrincipalBudget.HostBudget) {Ct eps J : ℝ} (hCt : 1 ≤ Ct)
    (heps : 0 < eps) (htiny : eps < 1/52) (e : ℝ → ℕ) (hpage : ∀ x ≥ (1:ℝ), PageN eps x (e x))
    (hJ : 1 ≤ J) (dyadic : WindowAt J eps (BaAt (AbF.ofChar PChar.one) eps e (fun z => ⌊z^Ct⌋₊))) :
    WindowAt J eps (fun q d x => VAt PChar.one eps Ct q d (e x) x) := by
  obtain ⟨r₁,r₂,x₀,_,_,scale⟩ := Principia.Ordinary.DyadicTransfer.from_budget budget eps Ct heps htiny
  obtain ⟨X₀,dy⟩ := dyadic
  have jpos : 0<J := by linarith
  let S := [PChar.one.N,ordC PChar.one,pK PChar.one,hStar PChar.one,pOne PChar.one,r₁,r₂].toFinset
  obtain ⟨XB,large⟩ := eventually_winPair_gt_power eps J Ct ((S.sup id : ℕ) : ℝ) heps jpos
  obtain ⟨Y₀,logbound⟩ := log_mul_le_rpow_of_winPair eps heps
  let L := max 2 (max x₀ Y₀)
  have hL : 2 ≤ L := le_max_left _ _
  have hLX : x₀ ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hLY : Y₀ ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨max (max X₀ XB) (L^J),?_⟩
  intro X hX q d pair
  have hlow : L ≤ X^(1/J) := by
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith : 0≤L) J)
      ((le_max_right _ _).trans hX) (one_div_pos.mpr jpos).le
    rwa [←Real.rpow_mul (by linarith : 0≤L),mul_one_div_cancel jpos.ne',Real.rpow_one] at hh
  obtain ⟨Y,hYX,hYY,H⟩ := dy X ((le_max_left _ _).trans ((le_max_left _ _).trans hX)) q d pair
  obtain ⟨hq,hd,hqr,hdr⟩ := large X ((le_max_right _ _).trans ((le_max_left _ _).trans hX)) q d pair
  have hb (a : ℕ) (ha : a ∈ S) : a<q ∧ a<d := by
    have hr : (a:ℝ) ≤ ((S.sup id : ℕ) : ℝ) := by exact_mod_cast (Finset.le_sup (f:=id) ha)
    exact ⟨by exact_mod_cast hr.trans_lt hqr,by exact_mod_cast hr.trans_lt hdr⟩
  have hr₁ := hb r₁ (by simp [S])
  have hr₂ := hb r₂ (by simp [S])
  have pp : PrimePair PChar.one.N q d :=
    ⟨pair.q_prime,pair.q_mod,pair.d_prime,pair.d_mod,Nat.coprime_one_right _⟩
  have adm := admissible_of_pageN heps htiny hCt hpage
  have logpair := logbound _ (hLY.trans hlow) q d pair
  refine ⟨Y,hYX,hYY,?_⟩
  intro x hxy hxy₂
  let t := ⌊x^Ct⌋₊
  have hWx := hYX.trans hxy
  have h2 : 2 ≤ x := hL.trans (hlow.trans hWx)
  have hxpos : 0 ≤ x := by linarith
  obtain ⟨he,_,ht,htx⟩ := adm x h2
  let h : Host := ⟨PChar.one,e x,q,d,he,pp⟩
  have htX : (t:ℝ) ≤ X^Ct := htx.trans (Real.rpow_le_rpow hxpos (hxy₂.trans hYY) (by linarith))
  have big : h.Big t := by
    refine ⟨?_,?_,?_⟩
    · change 2*t+1<q
      exact_mod_cast (show 2*(t:ℝ)+1 < q by linarith)
    · change 2*t+1<d
      exact_mod_cast (show 2*(t:ℝ)+1 < d by linarith)
    · intro y hy
      apply hb y
      simp only [S,h,Host.q,Host.o,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hy ⊢
      tauto
  have hpow : 0 ≤ X^(1/J) := le_trans (by linarith : 0≤L) hlow
  exact scale x (hLX.trans (hlow.trans hWx)) h rfl hr₁.1 hr₁.2 hr₂.1 hr₂.2 ht big
    (hpage x (by linarith)) (logpair.trans (Real.rpow_le_rpow hpow hWx (by positivity))) (H x hxy hxy₂)

end Principia.Ordinary.DyadicWindows

namespace Principia.Ordinary.DyadicAvoidance

open NumberField Formalism.HC UpperTheory.Top UpperTheory.V UpperTheory.V.Win

def Exceptions (R : ℕ) (eta Ct eps : ℝ) (e : ℝ → ℕ) : Prop :=
  ∀ J : ℝ, 0 < J → ∃ x₀ : ℝ, ∀ (X : ℝ) (q d : ℕ), PrimePair 1 q d →
    Real.log ((q:ℝ)*d) ≤ X^(eps/(4*J)) → ∃ exc : Finset ℕ, exc.card ≤ R ∧
      ∀ x ≥ x₀, X^(1/J) ≤ x → x ≤ X → Good eta Ct exc x →
        BaAt (AbF.ofChar PChar.one) eps e (fun z => ⌊z^Ct⌋₊) q d x

def Window (J Ct eps : ℝ) (e : ℝ → ℕ) : Prop :=
  ∃ X₀ : ℝ, ∀ X ≥ X₀, ∀ q d : ℕ, WinPair eps (X^(1/J)) q d →
    ∃ Y : ℝ, InRange J X Y ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y^(2:ℝ) →
      BaAt (AbF.ofChar PChar.one) eps e (fun z => ⌊z^Ct⌋₊) q d x

theorem select_window (R : ℕ) (eta Ct eps : ℝ) (e : ℝ → ℕ)
    (hη : 0 < eta) (hle : eta ≤ Ct) (heps : 0 < eps)
    (exceptions : Exceptions R eta Ct eps e) : Window (2^(R+2)*(Ct/eta)^R) Ct eps e := by
  let J : ℝ := 2^(R+2)*(Ct/eta)^R
  have hCt := hη.trans_le hle
  have hJ : 0 < J := by dsimp [J]; positivity
  obtain ⟨x₀,H⟩ := exceptions J hJ
  obtain ⟨Y₀,logbound⟩ := log_mul_le_rpow_of_winPair eps heps
  let L := max 2 (max Y₀ x₀)
  have hL : 2 ≤ L := le_max_left _ _
  have hL₀ : 0 ≤ L := by linarith
  have hLY : Y₀ ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hLx : x₀ ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨max 2 (L^J),?_⟩
  intro X hX q d pair
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hX
  have hX0 : 0 ≤ X := by linarith
  have hlow : L ≤ X^(1/J) := by
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hL₀ _)
      ((le_max_right _ _).trans hX) (one_div_pos.mpr hJ).le
    rwa [←Real.rpow_mul hL₀,mul_one_div_cancel hJ.ne',Real.rpow_one] at hh
  have hlog := logbound _ (hLY.trans hlow) q d pair
  have hp : (X^(1/J))^(eps/4) = X^(eps/(4*J)) := by
    rw [←Real.rpow_mul hX0]
    congr 1
    field_simp
  rw [hp] at hlog
  obtain ⟨exc,small,bound⟩ := H X q d
    ⟨pair.q_prime,pair.q_mod,pair.d_prime,pair.d_mod,Nat.coprime_one_right _⟩ hlog
  obtain ⟨Y,hY,avoid⟩ := UpperTheory.V.Win.window R eta Ct X exc hη hle (by linarith) small
  exact ⟨Y,hY,fun x lo hi => bound x (hLx.trans (hlow.trans (hY.1.trans lo)))
    (hY.1.trans lo) (hi.trans hY.2) (avoid x lo hi)⟩

end Principia.Ordinary.DyadicAvoidance

namespace Principia.Ordinary.DyadicRankWindow

open NumberField Formalism.HC UpperTheory.Top UpperTheory.V UpperTheory.V.Two UpperTheory.V.Win

theorem exceptions (web : Principia.Ordinary.WeberBase.Weber) (towerBound : TowerBound)
    {CK Ct eps : ℝ} (hCK : 0 < CK) (hCt : 0 ≤ Ct) (heps : 0 < eps)
    (hK : LemmaK CK) (e : ℝ → ℕ) (admit : admitted 4 Ct e fun x => ⌊x^Ct⌋₊) :
    Principia.Ordinary.DyadicAvoidance.Exceptions 24 (eps/(2*CK)) Ct eps e := by
  intro J hJ
  let M := AbF.ofChar PChar.one
  obtain ⟨x₀,H⟩ := partA CK hCK hK M 24 J Ct eps 4 hJ hCt heps
  refine ⟨x₀,fun X q d pair hlog => ?_⟩
  obtain ⟨L,_,_,hL⟩ := abExists (base2 M q d)
  have tower := (Principia.Ordinary.WeberTower.tower web q d pair L hL).2
  exact H e _ admit X q d pair hlog L (twoBase M q d pair L hL) (towerBound 2 L 24 tower)

theorem explicit_window (web : Principia.Ordinary.WeberBase.Weber) (towerBound : TowerBound)
    {CK Ct eps : ℝ} (hCK : 1 ≤ CK) (hCt : 1 ≤ Ct) (heps : 0 < eps) (htiny : eps < 1/52)
    (hK : LemmaK CK) (e : ℝ → ℕ) (admit : admitted 4 Ct e fun x => ⌊x^Ct⌋₊) :
    Principia.Ordinary.DyadicAvoidance.Window ((2:ℝ)^26*(2*CK*Ct/eps)^24) Ct eps e := by
  have hCK₀ : 0 < CK := by linarith
  have hη : 0 < eps/(2*CK) := by positivity
  have small : eps/(2*CK) ≤ Ct := by
    apply le_trans _ hCt
    rw [div_le_one (by positivity)]
    linarith
  have h := Principia.Ordinary.DyadicAvoidance.select_window 24 (eps/(2*CK)) Ct eps e hη small heps
    (exceptions web towerBound hCK₀ (by linarith) heps hK e admit)
  rwa [show Ct/(eps/(2*CK)) = 2*CK*Ct/eps by rw [div_div_eq_mul_div]; ring] at h

end Principia.Ordinary.DyadicRankWindow

namespace Principia.Ordinary.ExplicitPrincipalWindow

open NumberField Formalism.HC UpperTheory.Top UpperTheory.V UpperTheory.V.HV UpperTheory.V.Odd UpperTheory.V.Two

def exponent (CK Ct eps : ℝ) : ℝ := 2^26*(2*CK*Ct/eps)^24

theorem transfer (budget : Principia.Ordinary.PrincipalBudget.HostBudget) {CK Ct eps : ℝ}
    (hCK : 1 ≤ CK) (hCt : 1 ≤ Ct) (heps : 0 < eps) (htiny : eps < 1/52)
    (e : ℝ → ℕ) (page : ∀ x ≥ (1:ℝ), PageN eps x (e x))
    (dyadic : Principia.Ordinary.DyadicAvoidance.Window (exponent CK Ct eps) Ct eps e) :
    Principia.Ordinary.DyadicWindows.WindowAt (exponent CK Ct eps) eps (fun q d x => VAt PChar.one eps Ct q d (e x) x) := by
  have hratio : 1 ≤ 2*CK*Ct/eps := by
    rw [one_le_div heps]
    nlinarith [mul_le_mul_of_nonneg_right hCK (by linarith : 0 ≤ Ct)]
  have hJ : 1 ≤ exponent CK Ct eps := one_le_mul_of_one_le_of_one_le
    (by norm_num) (one_le_pow₀ hratio)
  apply Principia.Ordinary.DyadicWindows.at_index budget hCt heps htiny e page hJ
  obtain ⟨X₀,H⟩ := dyadic
  refine ⟨X₀,fun X hx q d pair => ?_⟩
  obtain ⟨Y,range,good⟩ := H X hx q d pair
  exact ⟨Y,range.1,range.2,good⟩

end Principia.Ordinary.ExplicitPrincipalWindow

namespace Principia.Ordinary.ArithmeticWindowRH

open NumberField Formalism.HC Formalism.GaloisCohomology UpperTheory.Top
open UpperTheory.V UpperTheory.V.HV UpperTheory.V.Odd

theorem principal_vwin_of_budget (web : WeberBase.Weber) (budget : PrincipalBudget.HostBudget)
    (pt : GlobalTheory.Published.PoitouTateDuality) (lf : LocalFinitenessK)
    (ltate : LocalTateDualityK) : VWinAt PChar.one 401 := by
  obtain ⟨C, hC⟩ := TwistCohomologyBound.exists_exponent pt lf ltate
  let K := max C 1
  have hK : 1 ≤ K := le_max_right _ _
  have hbound := Win.kmono C K (le_max_left _ _) hC
  intro ε hε hsmall e page
  have hratio : 1 ≤ 2 * K * 401 / ε := (one_le_div hε).mpr (by linarith)
  refine ⟨ExplicitPrincipalWindow.exponent K 401 ε, ?_, ?_⟩
  · exact one_le_mul_of_one_le_of_one_le (by norm_num : (1:ℝ) ≤ 2^26) (one_le_pow₀ hratio)
  · exact ExplicitPrincipalWindow.transfer budget hK (by norm_num) hε hsmall e page
      (DyadicRankWindow.explicit_window web (PropA.aBound_of_isTower pt lf ltate)
        hK (by norm_num) hε hsmall hbound e
        (admissible_of_pageN hε hsmall (by norm_num : (1 : ℝ) ≤ 401) page))

end Principia.Ordinary.ArithmeticWindowRH

namespace Principia.Ordinary.ConductorOneRH

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.HC
open GlobalTheory.EX UpperTheory.Top UpperTheory.V UpperTheory.V.HV UpperTheory.V.Odd
open CompanionTheory.LocalTateOrthogonality.Gcoh

def Height : Prop :=
  ∃ C r₁ r₂ : ℕ, r₁.Prime ∧ r₂.Prime ∧ ∀ h : Host, h.chi = PChar.one →
    r₁ < h.q1 → r₁ < h.d → r₂ < h.q1 → r₂ < h.d → ∀ t : ℕ, 2 ≤ t → h.Big t →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
      IsChiField PChar.one h.ex h.q1 h.d E → VVplusLe E t (((h.N : ℝ) * t) ^ C)

def LogCubeHeight : Prop :=
  ∃ C r₁ r₂ : ℕ, r₁.Prime ∧ r₂.Prime ∧ ∀ h : Host, h.chi = PChar.one →
    r₁ < h.q1 → r₁ < h.d → r₂ < h.q1 → r₂ < h.d → ∀ t : ℕ, 2 ≤ t → h.Big t →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
      IsChiField PChar.one h.ex h.q1 h.d E → VVplusLe E t (Real.exp ((C:ℝ) * (1 + Real.log ((h.N:ℝ)*t))^3))

theorem logCube_of_height (height : Height) : LogCubeHeight := by
  obtain ⟨C,r₁,r₂,h₁,h₂,H⟩ := height
  refine ⟨C,r₁,r₂,h₁,h₂,?_⟩
  intro h one h1q h1d h2q h2d t ht big E _ _ _ field Ω _ _ _ ld
  have original := H h one h1q h1d h2q h2d t ht big E field Ω ld
  have hn : 1 ≤ (h.N : ℝ) * t := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast h.N_pos) (by exact_mod_cast (show 1 ≤ t by omega))
  exact ⟨original.1,fun S hS => (original.2 S hS).trans (Growth.power_le_logCube hn C)⟩

theorem budget_of_logCube (height : LogCubeHeight) : PrincipalBudget.HostBudget := by
  obtain ⟨C,r₁,r₂,h₁,h₂,H⟩ := height
  refine ⟨C,r₁,r₂,h₁,h₂,?_⟩
  intro h he h1q h1d h2q h2d t ht hbig E _ _ _ hE B₂ htwo
  have hp : PrimePair (AbF.ofChar PChar.one).m h.q1 h.d := by
    change PrimePair PChar.one.N h.q1 h.d
    rw [← he]
    exact h.pair
  obtain ⟨c, bound⟩ := thmBcFree_of (ML.iv ClassicalWindowRH.duality
    GlobalTheory.CompanionTheory.Hypotheses₂.unramifiedOrthogonality)
  have hminus := bound (AbF.ofChar PChar.one) h.ex t h.q1 h.d h.two_le ht hp E
    ((isCompField_ofChar _ _ _ _ _).mpr hE)
  rw [Principia.Ordinary.PrincipalPrimes.minus_estimate] at hminus
  exact vvle_of_parts htwo hminus (H h he h1q h1d h2q h2d t ht hbig E hE)

theorem budget_of_height (height : Height) : PrincipalBudget.HostBudget :=
  budget_of_logCube (logCube_of_height height)

theorem principal_window_of_logCube (height : LogCubeHeight) (weber : WeberBase.Weber) : VWinAt PChar.one 401 :=
  ArithmeticWindowRH.principal_vwin_of_budget weber (budget_of_logCube height)
    ClassicalWindowRH.duality top_locfin top_tate

theorem principal_window (height : Height) (weber : WeberBase.Weber) : VWinAt PChar.one 401 :=
  ArithmeticWindowRH.principal_vwin_of_budget weber (budget_of_height height)
    ClassicalWindowRH.duality top_locfin top_tate

end Principia.Ordinary.ConductorOneRH

namespace Principia.Ordinary.ConductorOneRH

open Formalism.BasicNotions Formalism.MainNotions Formalism.HC GlobalTheory.EX UpperTheory.Top

/-- The principal character on the connected family detects the zeros of ordinary zeta. -/
theorem rh_of_connected (families : FamilyClassConnected ((GChi PChar.one).cls (3 / 2))) :
    RiemannHypothesis := by
  have w : ChebyshevInequalityAtWindowScale (Fam := FamP) (fun Fm => Fm.toFamCore)
      (fun Fm => ChainTied Fm) (3 / 2) (Level.cyc PChar.one) := by
    obtain ⟨d,l,ε₁,h₁,supply⟩ := families
    refine ⟨d,l,ε₁,h₁,fun ε he hsmall => ?_⟩
    obtain ⟨Fm,clas,tied⟩ := supply ε he hsmall
    exact ⟨Fm,eFamC_of_cls PChar.one _ Fm clas,clas.1,tied⟩
  have zero := level_of_tiedWin (Fam := FamP) (core := fun Fm => Fm.toFamCore)
    (Tied := fun Fm => ChainTied Fm)
    (UpperTheory.Comparison₂.level_gm_le_on_family_scales (Level.cyc PChar.one))
    (UpperTheory.Comparison₂.formB (Level.cyc PChar.one) (3 / 2) (by norm_num)) w
  apply Formalism.VW.rh_of_right
  intro s hs _
  have hz := zero PChar.one (Level.mem_cyc PChar.one) s hs
  change DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s ≠ 0 at hz
  simpa only [DirichletCharacter.LFunction_modOne_eq] using hz

/-- Weber's theorem and two geometric assertions for the trivial character imply ordinary RH. -/
theorem rh (weber : WeberBase.Weber) (height : Height)
    (connect : HostExW (3 / 2) (GChi PChar.one).req →
      FamilyClassConnected ((GChi PChar.one).cls (3 / 2))) : RiemannHypothesis :=
  rh_of_connected (connect (supplyChi PChar.one (principal_window height weber)))

/-- The height estimate may grow faster than every fixed polynomial in Nt. -/
theorem rh_of_logCube (weber : WeberBase.Weber) (height : LogCubeHeight)
    (connect : HostExW (3 / 2) (GChi PChar.one).req →
      FamilyClassConnected ((GChi PChar.one).cls (3 / 2))) : RiemannHypothesis :=
  rh_of_connected (connect (supplyChi PChar.one (principal_window_of_logCube height weber)))

end Principia.Ordinary.ConductorOneRH

end

#print axioms Principia.Ordinary.TwistCohomologyBound.exists_exponent
#print axioms Principia.Ordinary.ConductorOneRH.budget_of_height
#print axioms Principia.Ordinary.ConductorOneRH.principal_window
#print axioms Principia.Ordinary.ConductorOneRH.rh_of_connected
#print axioms Principia.Ordinary.ConductorOneRH.rh
#print axioms Principia.Ordinary.Growth.cube_absorbed
#print axioms Principia.Ordinary.Growth.power_le_logCube
#print axioms Principia.Ordinary.ConductorOneRH.logCube_of_height
#print axioms Principia.Ordinary.ConductorOneRH.principal_window_of_logCube
#print axioms Principia.Ordinary.ConductorOneRH.rh_of_logCube
