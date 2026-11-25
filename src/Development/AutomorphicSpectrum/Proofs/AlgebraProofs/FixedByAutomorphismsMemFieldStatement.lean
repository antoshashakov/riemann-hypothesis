module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Supplements.MathlibImports.AnalysisAndTactics
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.MemOfFixedByAutomorphisms

@[expose] public section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.fixed_by_automorphisms_mem_field : ∀ (F : IntermediateField ℚ ℂ) (c : ℂ), FiniteDimensional ℚ F → (∀ g : ℂ ≃+* ℂ, (∀ a ∈ F, g a = a) → g c = c) → c ∈ F :=
  @_root_.PositivityTheory.Xgn.mem_of_fixed_by_automorphisms
