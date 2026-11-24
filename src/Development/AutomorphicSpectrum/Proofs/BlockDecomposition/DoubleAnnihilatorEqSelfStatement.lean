module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleAnnihilatorEqSelf
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.double_annihilator_eq_self : ∀ (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X] [Module (ZMod n) X] [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y] (B : Y →ₗ[ZMod n] X →ₗ[ZMod n] ZMod n), Function.Injective B → Function.Injective B.flip → ∀ U : Submodule (ZMod n) X, (⨅ y ∈ (⨅ x ∈ U, LinearMap.ker (B.flip x)), LinearMap.ker (B y)) = U := by
  first | exact @GlobalTheory.CompanionTheory.FiniteDuality.double_annihilator | exact GlobalTheory.CompanionTheory.FiniteDuality.double_annihilator | (intros; apply GlobalTheory.CompanionTheory.FiniteDuality.double_annihilator <;> assumption)
