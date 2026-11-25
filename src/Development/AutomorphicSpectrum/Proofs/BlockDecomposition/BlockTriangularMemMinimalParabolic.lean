module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Supplements.LinearAlgebra.LeviCore

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.KFin.LeviPt

section Abstract

variable {K : Type} [CommRing K] (c : K →+* K)

theorem cT_add {m p : Type} (M N : Matrix m p K) : cT c (M + N) = cT c M + cT c N := by
  exact Formalism.UG.LeviCore.cT_add c M N

theorem cT_sub {m p : Type} (M N : Matrix m p K) : cT c (M - N) = cT c M - cT c N := by
  exact Formalism.UG.LeviCore.cT_sub c M N

theorem cT_cT (hc : ∀ x, c (c x) = x) {m p : Type} (M : Matrix m p K) : cT c (cT c M) = M := by
  exact Formalism.UG.LeviCore.cT_cT c hc M

theorem cT_diagonal {m : Type} [DecidableEq m] (d : m → K) :
    cT c (diagonal d) = diagonal (fun i => c (d i)) := by
  exact Formalism.UG.LeviCore.cT_diagonal c d

theorem levi_core (hc : ∀ x, c (c x) = x) {n r : ℕ} {Jh : Matrix (Fin n) (Fin n) K}
    {Xa Ya : Matrix (Fin n) (Fin r) K} {Xd Yd : Matrix (Fin r) (Fin n) K}
    (hJ : cT c Jh = Jh) (hXd : Xd = cT c Xa * Jh) (hYd : Yd = cT c Ya * Jh)
    (hxx : Xd * Xa = 0) (hyy : Yd * Ya = 0) (hxy : Xd * Ya = 1)
    (g : GL (Fin n) K) (hg : cT c (g : Matrix (Fin n) (Fin n) K) * Jh * (g : Matrix (Fin n) (Fin n) K) = Jh)
    (B : Matrix (Fin r) (Fin r) K) (hBt : B.BlockTriangular id)
    (hB : (g : Matrix (Fin n) (Fin n) K) * Xa = Xa * B)
    (L : Matrix (Fin n) (Fin n) K)
    (hL : L = Xa * diagonal (fun i => (Yd * (g : Matrix (Fin n) (Fin n) K) * Xa) i i) * Yd
      + Ya * diagonal (fun i => (Xd * (g : Matrix (Fin n) (Fin n) K) * Ya) i i) * Xd
      + (1 - Xa * Yd - Ya * Xd) * (g : Matrix (Fin n) (Fin n) K) * (1 - Xa * Yd - Ya * Xd)) :
    ∃ u : GL (Fin n) K, (u : Matrix (Fin n) (Fin n) K) = L ∧ cT c L * Jh * L = Jh ∧
      (∃ d, L * Xa = Xa * diagonal d) ∧ (∃ d', L * Ya = Ya * diagonal d') ∧
      (∃ B' : Matrix (Fin r) (Fin r) K, B'.BlockTriangular id ∧ (∀ i, B' i i = 1) ∧
        ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) * Xa = Xa * B') ∧
      ∀ z : Fin n → K, Xd *ᵥ z = 0 → ∃ a : Fin r → K,
        (((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) - 1) *ᵥ z = Xa *ᵥ a := by
  exact Formalism.UG.LeviCore.levi_core c hc hJ hXd hYd hxx hyy hxy g hg B hBt hB L hL

end Abstract

section Place

theorem sigma_invol {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x :=
  _root_.GlobalTheory.AdelicU.cm_conj_conj h x

theorem sigR_invol {F E : Type} [Field F] [Field E] [Algebra F E] (A : Type) [CommRing A] [Algebra F A]
    {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (x : A ⊗[F] E) : sigR A σ (sigR A σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem sigR_inclR {F E : Type} [Field F] [Field E] [Algebra F E] (A : Type) [CommRing A] [Algebra F A]
    (σ : E →ₐ[F] E) (e : E) : sigR A σ (inclR A e) = inclR A (σ e) := by
  simp [sigR, inclR]

theorem cT_map_inclR {F E : Type} [Field F] [Field E] [Algebra F E] (A : Type) [CommRing A] [Algebra F A]
    (σ : E →ₐ[F] E) {a b : ℕ} (N : Matrix (Fin a) (Fin b) E) :
    cT (sigR A σ) (N.map (inclR (F := F) A)) = (cT (σ : E →+* E) N).map (inclR (F := F) A) := by
  ext i j; simp [cT, sigR_inclR]

theorem exists_levi : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (A : Type) [CommRing A] [Algebra F A] [TopologicalSpace A] (p : HA A σ J) (B : Matrix (Fin r) (Fin r) (A ⊗[F] E)), B.BlockTriangular id → (matHom A σ J p).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * B → ∃ m : HA A σ J, (matHom A σ J m).1 = leviMat σ J A X Y (matHom A σ J p).1 ∧ (∃ d : Fin r → A ⊗[F] E, (matHom A σ J m).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * diagonal d) ∧ (∃ d' : Fin r → A ⊗[F] E, (matHom A σ J m).1 * Y.map (inclR (F := F) A) = Y.map (inclR (F := F) A) * diagonal d') ∧ (∃ B' : Matrix (Fin r) (Fin r) (A ⊗[F] E), B'.BlockTriangular id ∧ (∀ i, B' i i = 1) ∧ (matHom A σ J (m⁻¹ * p)).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * B') ∧ ∀ z : Fin n → A ⊗[F] E, ((cT (σ : E →+* E) X * J).map (inclR (F := F) A)) *ᵥ z = 0 → ∃ a : Fin r → A ⊗[F] E, ((matHom A σ J (m⁻¹ * p)).1 - 1) *ᵥ z = X.map (inclR (F := F) A) *ᵥ a := by
  intro F E _ _ _ _ _ σ n J r X Y hCM hJ hW A _ _ _ p B hBt hB
  have hc := sigR_invol A (sigma_invol hCM)
  have hJh : cT (sigR A σ) (J.map (inclR (F := F) A)) = J.map (inclR (F := F) A) := by
    rw [cT_map_inclR]; congr 1; ext i j; exact hJ.1 i j
  have hmap0 : ((0 : Matrix (Fin r) (Fin r) E)).map (inclR (F := F) A) = 0 := by simp
  have hmap1 : ((1 : Matrix (Fin r) (Fin r) E)).map (inclR (F := F) A) = 1 := by simp
  have hg : cT (sigR A σ) ((matHom A σ J p : GL (Fin n) (A ⊗[F] E)) : Matrix (Fin n) (Fin n) (A ⊗[F] E)) *
      J.map (inclR (F := F) A) * ((matHom A σ J p : GL (Fin n) (A ⊗[F] E)) : Matrix (Fin n) (Fin n) (A ⊗[F] E)) =
      J.map (inclR (F := F) A) := by
    have h : matHom A σ J p ∈ HR A σ J := (show ↥(HR A σ J) from p).2
    exact h
  have hXd : (cT (σ : E →+* E) X * J).map (inclR (F := F) A) =
      cT (sigR A σ) (X.map (inclR (F := F) A)) * J.map (inclR (F := F) A) := by
    rw [Matrix.map_mul, cT_map_inclR]
  have hYd : (cT (σ : E →+* E) Y * J).map (inclR (F := F) A) =
      cT (sigR A σ) (Y.map (inclR (F := F) A)) * J.map (inclR (F := F) A) := by
    rw [Matrix.map_mul, cT_map_inclR]
  have hxx : (cT (σ : E →+* E) X * J).map (inclR (F := F) A) * X.map (inclR (F := F) A) = 0 := by
    rw [← Matrix.map_mul, hW.xx, hmap0]
  have hyy : (cT (σ : E →+* E) Y * J).map (inclR (F := F) A) * Y.map (inclR (F := F) A) = 0 := by
    rw [← Matrix.map_mul, hW.yy, hmap0]
  have hxy : (cT (σ : E →+* E) X * J).map (inclR (F := F) A) * Y.map (inclR (F := F) A) = 1 := by
    rw [← Matrix.map_mul, hW.xy, hmap1]
  obtain ⟨u, hu, hunit, hXa, hYa, hB', hz⟩ := levi_core (sigR A σ) hc hJh hXd hYd hxx hyy hxy
    (matHom A σ J p) hg B hBt hB (leviMat σ J A X Y (matHom A σ J p).1) rfl
  have hmem : u ∈ HR A σ J := by
    show cT (sigR A σ) (u : Matrix (Fin n) (Fin n) (A ⊗[F] E)) * J.map (inclR (F := F) A) *
      (u : Matrix (Fin n) (Fin n) (A ⊗[F] E)) = J.map (inclR (F := F) A)
    rw [hu]; exact hunit
  let m : HA A σ J := (⟨u, hmem⟩ : ↥(HR A σ J))
  have hmu : matHom A σ J m = u := rfl
  have e : ((matHom A σ J (m⁻¹ * p) : GL (Fin n) (A ⊗[F] E)) : Matrix (Fin n) (Fin n) (A ⊗[F] E)) =
      ((u⁻¹ : GL (Fin n) (A ⊗[F] E)) : Matrix (Fin n) (Fin n) (A ⊗[F] E)) *
        ((matHom A σ J p : GL (Fin n) (A ⊗[F] E)) : Matrix (Fin n) (Fin n) (A ⊗[F] E)) := by
    rw [map_mul, map_inv, Units.val_mul, hmu]
  refine ⟨m, by rw [hmu]; exact hu, by rw [hmu, hu]; exact hXa, by rw [hmu, hu]; exact hYa, ?_, ?_⟩
  · obtain ⟨B', h1, h2, h3⟩ := hB'
    exact ⟨B', h1, h2, by rw [e]; exact h3⟩
  · intro z hz0
    obtain ⟨a, ha⟩ := hz z hz0
    exact ⟨a, by rw [e]; exact ha⟩

end Place

end GlobalTheory.CompanionTheory.KFin.LeviPt
