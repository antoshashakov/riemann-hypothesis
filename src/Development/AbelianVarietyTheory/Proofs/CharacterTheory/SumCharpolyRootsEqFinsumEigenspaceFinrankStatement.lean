module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.SumCharpolyRootsEqFinsumEigenspaceFinrank
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.sum_charpoly_roots_eq_finsum_eigenspace_finrank : ∀ (k : Type) [Field k] [IsAlgClosed k] (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (g : Module.End k V) (N : ℕ), (N : k) ≠ 0 → g ^ N = 1 → ∀ h : k → ℂ, ((LinearMap.charpoly g).roots.map h).sum = ∑ᶠ μ ∈ {μ : k | μ ^ N = 1}, (Module.finrank k (Module.End.eigenspace g μ) : ℂ) * h μ := by
  first | exact @GlobalTheory.CuspGL.sum_roots_charpoly_eq_finsum_eigenspace | exact GlobalTheory.CuspGL.sum_roots_charpoly_eq_finsum_eigenspace | (intros; apply GlobalTheory.CuspGL.sum_roots_charpoly_eq_finsum_eigenspace <;> assumption)
