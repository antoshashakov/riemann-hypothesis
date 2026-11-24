module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsLevi
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
import CompanionTheory.ThickeningEstimates.LieGroupReduction.SiegelCore
import Supplements.LinearAlgebra.LeviCore

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet CompanionTheory.ThKR GlobalTheory.CompanionTheory.KFin
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
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨_, _, _, hτ⟩ := h
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  apply w.embedding.injective
  rw [hτ, hτ, star_star]

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

theorem exists_levi : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (A : Type) [CommRing A] [Algebra F A] [TopologicalSpace A] (p : HA A σ J) (B : Matrix (Fin r) (Fin r) (A ⊗[F] E)), B.BlockTriangular id → (matHom A σ J p).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * B → ∃ m : HA A σ J, (matHom A σ J m).1 = leviMat σ J A X Y (matHom A σ J p).1 ∧ (∃ d : Fin r → A ⊗[F] E, (matHom A σ J m).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * diagonal d) ∧ (∃ d' : Fin r → A ⊗[F] E, (matHom A σ J m).1 * Y.map (inclR (F := F) A) = Y.map (inclR (F := F) A) * diagonal d') ∧ (∃ B' : Matrix (Fin r) (Fin r) (A ⊗[F] E), B'.BlockTriangular id ∧ (∀ i, B' i i = 1) ∧ (matHom A σ J (m⁻¹ * p)).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * B') ∧ ∀ z : Fin n → A ⊗[F] E, ((cT (σ : E →+* E) X * J).map (inclR (F := F) A)) *ᵥ z = 0 → ∃ a : Fin r → A ⊗[F] E, ((matHom A σ J (m⁻¹ * p)).1 - 1) *ᵥ z = X.map (inclR (F := F) A) *ᵥ a :=
  _root_.UpperTheory.Reformulated.B.Gka3.exists_levi

end Place

end GlobalTheory.CompanionTheory.KFin.LeviPt
