module

import Supplements.Lattices.FourfoldCarrierProofs
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PHfArith
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PSelfDual
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdChar
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstUniqueOf
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.CayleyGaussianIntegralsCongrFact
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlockFirstBlockEmb
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Th0CharMulOpUTh0HalfPeriodEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions Classical

namespace GlobalTheory.FourthRootStd

open Supplements.Lattices

section
variable (D : D7)

theorem mem_stdL {N : ℕ} (x : Fin N → D.host.E) :
    x ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N ↔ ∀ i, x i ∈ (algebraMap (𝓞 D.host.E) D.host.E).range :=
  FourfoldCarrierProofs.mem_stdL (Formalism.L2.Ker.Car.ofRec D) x

theorem single_mem_stdL {N : ℕ} (a : Fin N) : (Pi.single a 1 : Fin N → D.host.E) ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N :=
  FourfoldCarrierProofs.single_mem_stdL (Formalism.L2.Ker.Car.ofRec D) a

theorem star_mem_range (x : D.host.E) (h : x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) :
    (letI := D.host.cmStar; star x) ∈ (algebraMap (𝓞 D.host.E) D.host.E).range :=
  FourfoldCarrierProofs.star_mem_range (Formalism.L2.Ker.Car.ofRec D) x h

theorem stdL_isSD (N : ℕ) : (letI := D.host.cmStar; IsSDLat D.host.E N (Formalism.MainNotions.StandardLatticesGL3.stdL D N)) :=
  FourfoldCarrierProofs.stdL_isSD (Formalism.L2.Ker.Car.ofRec D) N

theorem Adm_std (N N' : ℕ) (h : Even N) (h' : Even N') :
    Formalism.MainNotions.TaylorLogMetric.admitted D N N' (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N') :=
  ⟨h, h', stdL_isSD D N, stdL_isSD D N'⟩

end

open Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity
open Formalism.L2.Th1.F (cmTheta)

theorem formV_apply (A : ℝ) (n : Type) [Fintype n] (N N' : ℕ) (z w : n → Fin N' → Fin N → ℂ) :
    formV A n N N' z w = (∑ τ, ∑ i, ∑ j, z τ i j * conj (w τ i j)) / (A : ℂ) := rfl

section
variable {n : Type} [Fintype n] [DecidableEq n]

theorem matH_hOne (L : PeriodPair) (z w : n → ℂ) :
    matH (hOne L n) z w = (∑ τ, z τ * conj (w τ)) / ((Formalism.L2.Th1.F.area L : ℝ) : ℂ) := by
  show (∑ i, ∑ j, z i * hOne L n i j * conj (w j)) = _
  simp only [hOne, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [div_eq_mul_inv]; ring

end

theorem area_eq (L : PeriodPair) : TaylorLogMetric.area L.lattice.toAddSubgroup = Formalism.L2.Th1.F.area L :=
  FourfoldCarrierProofs.area_eq L

theorem areaOK {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) : B.AreaOK :=
  FourfoldCarrierProofs.areaOK B.toCar

theorem omega_mem {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) : B.ω₀ ∈ B.L.lattice :=
  FourfoldCarrierProofs.omega_mem B.toCar

theorem stdOK_of {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)
    (half : B.ω₀ / 2 ∉ B.L.lattice)
    (isom : IsIsom (matH (blk4 (hOne B.L D.what₂.Tau))) (stdH B.L (Fin 4 × D.what₂.Tau))
      (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)))
    (betaStd : ∀ x ∈ stdLat B.L (Fin 4 × D.what₂.Tau),
      alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau)) x = stdChar B.L B.ω₀ x)
    (betaSemi : IsSemiChar (stdH B.L (Fin 4 × D.what₂.Tau))
      (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM))
      (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))))
    (selfDual : IsSelfDual (stdH B.L (Fin 4 × D.what₂.Tau))
      (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)))
    (idx₁ : relIdx (stdLat B.L (Fin 4 × D.what₂.Tau))
      (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)) ≠ 0)
    (idx₂ : relIdx (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM))
      (stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0) : B.StdOK :=
  { per := omega_mem B
    half := half
    isom := isom
    alpha0 := by simp [alphaQ, qOf]
    betaStd := betaStd
    betaSemi := betaSemi
    betaAlpha := fun x => by
      rw [← quadMultiplierRules.2]
      exact quadMultiplierRules.1 _ _ _ _ _ isom _ x
    selfDual := selfDual
    idx₁ := idx₁
    idx₂ := idx₂ }

section Lat0

variable (D : D7) {N N' : ℕ}

theorem homL_std_entry {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ TaylorLogMetric.homL D (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (i : Fin N') (j : Fin N) :
    A i j ∈ (algebraMap (𝓞 D.host.E) D.host.E).range :=
  FourfoldCarrierProofs.homL_std_entry (D := Formalism.L2.Ker.Car.ofRec D) hA i j

theorem YYl_std_entry {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ TaylorLogMetric.YYl D (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (i : Fin N') (j : Fin N) :
    A i j ∈ D.host.AA0 :=
  FourfoldCarrierProofs.YYl_std_entry (D := Formalism.L2.Ker.Car.ofRec D) hA i j

theorem single_mem_homL (i : Fin N') (j : Fin N) :
    (Matrix.single i j (1 : D.host.E)) ∈ TaylorLogMetric.homL D (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') :=
  FourfoldCarrierProofs.single_mem_homL (D := Formalism.L2.Ker.Car.ofRec D) i j

def putE (D : D7) (N N' : ℕ) (i : Fin N') (j : Fin N) : (D.what₂.Tau → ℂ) →+ TaylorLogMetric.VC D N N' where
  toFun v := fun τ i' j' => if i' = i ∧ j' = j then v τ else 0
  map_zero' := by funext τ i' j'; simp
  map_add' := by intro a b; funext τ i' j'; by_cases h : i' = i ∧ j' = j <;> simp [h]

theorem Lat0 (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') = powLat (lamMM D (TaylorLogMetric.lamOf D cc δ)) N N' := by
  let _ := @GlobalTheory.FourthRootStd.putE.eq_1
  exact FourfoldCarrierProofs.Lat0 (D := Formalism.L2.Ker.Car.ofRec D) cc δ

end Lat0

section
variable {D : D7}

def emb4 (D : D7) (x : Fin 4 → D.host.E) : Fin 4 × D.what₂.Tau → ℂ := fun w => TaylorLogMetric.embT D w.2 (x w.1)

theorem span_range_emb4_eq_top (D : D7) : Submodule.span ℂ (Set.range (emb4 D)) = ⊤ := by
  let _ := @GlobalTheory.FourthRootStd.emb4.eq_1
  exact FourfoldCarrierProofs.span_range_emb4_eq_top (Formalism.L2.Ker.Car.ofRec D)

theorem isoK_hermitian_sum_eq_emb4_hermitian_sum (γ : IsoK D) (x y : Fin 4 → D.host.E) :
    ∑ w, D.host.φ₀ ((γ.g x w : D.host.K) : D.host.E) * conj (D.host.φ₀ ((γ.g y w : D.host.K) : D.host.E))
      = ∑ w, emb4 D x w * conj (emb4 D y w) :=
  FourfoldCarrierProofs.isoK_hermitian_sum_eq_emb4_hermitian_sum (D := Formalism.L2.Ker.Car.ofRec D) γ x y

theorem blockFourfold_hOne_eq_hOne (L : PeriodPair) (n : Type) [Fintype n] [DecidableEq n] :
    blk4 (hOne L n) = hOne L (Fin 4 × n) :=
  FourfoldCarrierProofs.blockFourfold_hOne_eq_hOne L n

theorem isomOK {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) :
    IsIsom (matH (blk4 (hOne B.L D.what₂.Tau))) (stdH B.L (Fin 4 × D.what₂.Tau))
      (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) :=
  FourfoldCarrierProofs.isomOK B.toCar

end

theorem delta_ne_zero {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) : δ ≠ 0 := by
  intro h0
  subst h0
  have hz : TaylorLogMetric.lamOf D cc 0 = ⊥ := by
    unfold TaylorLogMetric.lamOf
    rw [AddSubgroup.closure_eq_bot_iff]
    rintro w ⟨c, -, rfl⟩
    simp
  have h1 : B.L.ω₁ ∈ B.L.lattice.toAddSubgroup := B.L.ω₁_mem_lattice
  rw [B.lat, hz, AddSubgroup.mem_bot] at h1
  have h2 := B.L.indep.ne_zero 0
  exact h2 (by simpa using h1)

theorem selfDual_La {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hcc : TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (hA : TaylorLogMetric.admitted D N N' L L') :
    IsSelfDual (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L') := by
  have hI := hermitian_form_integral_values D cc hcc δ hδ h0 N N' L L' hA
  apply le_antisymm
  · intro v hv
    exact self_dual_lattice D cc hcc δ hδ h0 N N' L L' hA v (fun y hy => hv y hy)
  · intro v hv y hy
    obtain ⟨a, b, -, hab⟩ := hI v hv y hy
    refine ⟨b, ?_⟩
    show (TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) v y).im = (b : ℝ)
    rw [hab]; simp

theorem selfDual_image {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (H : Sesq V) (H' : Sesq W)
    (g : V ≃ₗ[ℂ] W) (hg : IsIsom H H' (g : V →ₗ[ℂ] W)) (Λ : AddSubgroup V) (h : IsSelfDual H Λ) :
    IsSelfDual H' (imgLat (g : V →ₗ[ℂ] W) Λ) :=
  FourfoldCarrierProofs.selfDual_image H H' g hg Λ h

theorem exists_nat_mul (F : Type*) [Field F] [NumberField F] (T : Finset F) :
    ∃ m : ℕ, 0 < m ∧ ∀ x ∈ T, IsIntegral ℤ ((m : F) * x) :=
  FourfoldCarrierProofs.exists_nat_mul F T

theorem denom (E K : Type*) [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type*} [Fintype ι] (f : ι → E →+ K) :
    ∃ m : ℕ, 0 < m ∧ ∀ i, ∀ x : 𝓞 E, IsIntegral ℤ ((m : K) * f i (x : E)) :=
  FourfoldCarrierProofs.denom E K f

theorem fg_of_nsmul_le {ι : Type} (M M' : AddSubgroup (ι → ℂ)) [AddGroup.FG M'] (N : ℕ) (hN : 0 < N)
    (h : ∀ x ∈ M, N • x ∈ M') : AddGroup.FG M :=
  FourfoldCarrierProofs.fg_of_nsmul_le M M' N hN h

def e4 : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv

def reix (n : Type) : (n → Fin 2 → Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ) where
  toFun u := fun w => u w.2 (e4.symm w.1).1 (e4.symm w.1).2
  invFun z := fun τ i j => z (e4 (i, j), τ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv u := by funext τ i j; simp
  right_inv z := by funext ⟨a, τ⟩; simp

theorem reix_pow {n : Type} [Fintype n] (Λ : AddSubgroup (n → ℂ)) :
    imgLat (reix n : (n → Fin 2 → Fin 2 → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (powLat Λ 2 2) = pow4 Λ := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩ a
    exact hu (e4.symm a).1 (e4.symm a).2
  · intro hz
    exact ⟨(reix n).symm z, fun i j => hz (e4 (i, j)), (reix n).apply_symm_apply z⟩

theorem reix_isom (L : PeriodPair) (n : Type) [Fintype n] [DecidableEq n] :
    IsIsom (formV (Formalism.L2.Th1.F.area L) n 2 2) (matH (blk4 (hOne L n)))
      (reix n : (n → Fin 2 → Fin 2 → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) := by
  intro x y
  rw [blockFourfold_hOne_eq_hOne, matH_hOne, formV_apply]
  congr 1
  show ∑ w : Fin 4 × n, x w.2 (e4.symm w.1).1 (e4.symm w.1).2 * conj (y w.2 (e4.symm w.1).1 (e4.symm w.1).2)
    = ∑ τ, ∑ i, ∑ j, x τ i j * conj (y τ i j)
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have := Equiv.sum_comp e4.symm (fun p : Fin 2 × Fin 2 => x τ p.1 p.2 * conj (y τ p.1 p.2))
  rw [Fintype.sum_prod_type] at this
  exact this

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem lam_mul (o : 𝓞 D.host.K) {w : ℂ} (hw : w ∈ TaylorLogMetric.lamOf D cc δ) :
    D.host.φ₀ (((o : D.host.K) : D.host.E)) * w ∈ TaylorLogMetric.lamOf D cc δ :=
  FourfoldCarrierProofs.lam_mul (D := Formalism.L2.Ker.Car.ofRec D) o hw

theorem theta_eq (D : D7) : cmTheta 1 D.host.d = D.host.φ₀ (((AR.om D : D.host.K) : D.host.E)) :=
  FourfoldCarrierProofs.theta_eq (Formalism.L2.Ker.Car.ofRec D)

theorem lam_theta {w : ℂ} (hw : w ∈ TaylorLogMetric.lamOf D cc δ) : cmTheta 1 D.host.d * w ∈ TaylorLogMetric.lamOf D cc δ :=
  FourfoldCarrierProofs.lam_theta (D := Formalism.L2.Ker.Car.ofRec D) hw

theorem lamMM_smul (o : 𝓞 D.host.K) {v : D.what₂.Tau → ℂ} (hv : v ∈ lamMM D (TaylorLogMetric.lamOf D cc δ)) :
    D.host.φ₀ (((o : D.host.K) : D.host.E)) • v ∈ lamMM D (TaylorLogMetric.lamOf D cc δ) :=
  FourfoldCarrierProofs.lamMM_smul (D := Formalism.L2.Ker.Car.ofRec D) o hv

theorem gen_mem {Λ : AddSubgroup ℂ} {w : ℂ} (hw : w ∈ Λ) {y : Fin 4 → D.host.E} (hy : ∀ a, y a ∈ D.host.AA0) :
    w • emb4 D y ∈ pow4 (lamMM D Λ) :=
  fun a => AddSubgroup.subset_closure ⟨w, hw, y a, hy a, rfl⟩

def put4 (n : Type) (a : Fin 4) : (n → ℂ) →+ (Fin 4 × n → ℂ) where
  toFun v := fun w => if w.1 = a then v w.2 else 0
  map_zero' := by funext w; simp
  map_add' := by intro x y; funext w; by_cases h : w.1 = a <;> simp [h]

theorem fourth_power_le_closure_embeddings (Λ : AddSubgroup ℂ) : pow4 (lamMM D Λ) ≤
    AddSubgroup.closure {z | ∃ w ∈ Λ, ∃ y : Fin 4 → D.host.E, (∀ a, y a ∈ D.host.AA0) ∧ z = w • emb4 D y} := by
  let _ := @GlobalTheory.FourthRootStd.put4.eq_1
  exact FourfoldCarrierProofs.fourth_power_le_closure_embeddings (D := Formalism.L2.Ker.Car.ofRec D) Λ

theorem int_mem_inverse_half_different {x : D.host.E} (hx : IsIntegral ℤ x) : x ∈ D.host.AA0 :=
  FourfoldCarrierProofs.int_mem_inverse_half_different (D := Formalism.L2.Ker.Car.ofRec D) hx

theorem exists_nat_clearing_order_denominators (D : D7) : ∃ k : ℕ, 0 < k ∧ ∀ a ∈ D.host.AA0, IsIntegral ℤ ((k : D.host.E) * a) :=
  FourfoldCarrierProofs.exists_nat_clearing_order_denominators (Formalism.L2.Ker.Car.ofRec D)

section B

variable (B : Base D cc δ)

theorem mem_iff (x : ℂ) : x ∈ B.L.lattice ↔ x ∈ TaylorLogMetric.lamOf D cc δ :=
  FourfoldCarrierProofs.mem_iff B.toCar x

theorem hst : ∀ x ∈ B.L.lattice, cmTheta 1 D.host.d * x ∈ B.L.lattice :=
  fun x hx => (mem_iff B _).2 (lam_theta ((mem_iff B x).1 hx))

theorem theta_val (D : D7) : cmTheta 1 D.host.d = (1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 :=
  FourfoldCarrierProofs.theta_val (Formalism.L2.Ker.Car.ofRec D)

theorem hθ : cmTheta 1 D.host.d * (B.ω₀ / 2) ∉ B.L.lattice :=
  FourfoldCarrierProofs.hθ B.toCar

theorem hθ' : (1 - cmTheta 1 D.host.d) * (B.ω₀ / 2) ∉ B.L.lattice :=
  FourfoldCarrierProofs.hθ' B.toCar

theorem half : B.ω₀ / 2 ∉ B.L.lattice := SC.half_notMem (hst B) (omega_mem B) (hθ B) (hθ' B)

theorem betaStd : ∀ x ∈ stdLat B.L (Fin 4 × D.what₂.Tau),
    alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau)) x = stdChar B.L B.ω₀ x :=
  fun x hx => SC.stdChar_eq (hst B) (omega_mem B) (hθ B) (hθ' B) (by have := D.host.hyp.2.2.2.1; omega) _ x hx

theorem selfDual (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    IsSelfDual (stdH B.L (Fin 4 × D.what₂.Tau))
      (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)) :=
  FourfoldCarrierProofs.selfDual B.toCar hcc hδ

theorem betaSemi (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    IsSemiChar (stdH B.L (Fin 4 × D.what₂.Tau))
      (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM))
      (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))) :=
  FourfoldCarrierProofs.betaSemi B.toCar hcc hδ

theorem up : ∃ N : ℕ, 0 < N ∧
    ∀ x ∈ imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM),
      N • x ∈ stdLat B.L (Fin 4 × D.what₂.Tau) :=
  FourfoldCarrierProofs.up B.toCar

theorem down : ∃ N : ℕ, 0 < N ∧ ∀ x ∈ stdLat B.L (Fin 4 × D.what₂.Tau),
    N • x ∈ imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM) :=
  FourfoldCarrierProofs.down B.toCar

theorem idx₂ : relIdx (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM))
    (stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 :=
  FourfoldCarrierProofs.idx₂ B.toCar

theorem idx₁ : relIdx (stdLat B.L (Fin 4 × D.what₂.Tau))
    (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)) ≠ 0 :=
  FourfoldCarrierProofs.idx₁ B.toCar

theorem stdOK (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : B.StdOK :=
  stdOK_of B (half B) (isomOK B) (betaStd B) (betaSemi B hcc hδ) (selfDual B hcc hδ) (idx₁ B) (idx₂ B)

end B

theorem stdOK_of_crv : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ),
    StandardLatticesGL3.Crv D cc δ → B.StdOK :=
  fun _ _ _ B h => stdOK B h.1 h.2

end GlobalTheory.FourthRootStd
