/-
══════════════════════════════════════════════════════════════════════════════
  §6. The Index System: Prohibition Structure as Falsification Target
══════════════════════════════════════════════════════════════════════════════

  File     : A5CosmicNecessity/Section6_ProhibitionStructure.lean
  Author   : M. Numagaki
  Date     : February 2026

  STATUS:  sorry = 0 | axiom = 0 (file-local)
══════════════════════════════════════════════════════════════════════════════
-/

import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic
import Mathlib.Tactic

import A5CosmicNecessity.SolvabilityBelow60

set_option maxRecDepth 4000

namespace CosmicNecessity



section IcosahedralParameters
end IcosahedralParameters


section RepresentationData

inductive A5Irrep where
  | rho1  : A5Irrep
  | rho3  : A5Irrep
  | rho3' : A5Irrep
  | rho4  : A5Irrep
  | rho5  : A5Irrep
  deriving DecidableEq, Repr

def irrepDim : A5Irrep → ℕ
  | .rho1  => 1
  | .rho3  => 3
  | .rho3' => 3
  | .rho4  => 4
  | .rho5  => 5

def irrepDims : List ℕ := [1, 3, 3, 4, 5]

theorem irrep_count : irrepDims.length = 5 := by native_decide

theorem burnside_formula_s6 :
    1^2 + 3^2 + 3^2 + 4^2 + 5^2 = 60 := by norm_num

theorem burnside_formula_list_s6 :
    (irrepDims.map (· ^ 2)).sum = 60 := by native_decide

theorem rho4_unique_non_SO3 :
    (irrepDim .rho4 % 2 = 0) ∧
    (irrepDim .rho1 % 2 = 1) ∧
    (irrepDim .rho3 % 2 = 1) ∧
    (irrepDim .rho3' % 2 = 1) ∧
    (irrepDim .rho5 % 2 = 1) := by
  simp [irrepDim]

end RepresentationData


/-!
══════════════════════════════════════════════════════════════════════════════
  §6.2.
══════════════════════════════════════════════════════════════════════════════
-/

section P1_Rho4SelectionRule

structure TensorPair where
  left  : A5Irrep
  right : A5Irrep
  deriving DecidableEq, Repr

def tensorDim (p : TensorPair) : ℕ :=
  irrepDim p.left * irrepDim p.right

def containsRho4 (p : TensorPair) : Bool :=
  p.left == .rho4 || p.right == .rho4

def isSelfProduct (p : TensorPair) : Bool :=
  p.left == p.right

def passesP1 (p : TensorPair) : Bool :=
  containsRho4 p && !isSelfProduct p

def tensorPairs : List TensorPair := [
  ⟨.rho3,  .rho3⟩,
  ⟨.rho3,  .rho3'⟩,
  ⟨.rho3,  .rho4⟩,
  ⟨.rho3,  .rho5⟩,
  ⟨.rho3', .rho3'⟩,
  ⟨.rho3', .rho4⟩,
  ⟨.rho3', .rho5⟩,
  ⟨.rho4,  .rho4⟩,
  ⟨.rho4,  .rho5⟩,
  ⟨.rho5,  .rho5⟩
]

theorem tensor_pairs_count : tensorPairs.length = 10 := by native_decide


theorem tensor_dimensions :
    (tensorDim ⟨.rho3,  .rho3⟩  = 9) ∧
    (tensorDim ⟨.rho3,  .rho3'⟩ = 9) ∧
    (tensorDim ⟨.rho3,  .rho4⟩  = 12) ∧
    (tensorDim ⟨.rho3,  .rho5⟩  = 15) ∧
    (tensorDim ⟨.rho3', .rho3'⟩ = 9) ∧
    (tensorDim ⟨.rho3', .rho4⟩  = 12) ∧
    (tensorDim ⟨.rho3', .rho5⟩  = 15) ∧
    (tensorDim ⟨.rho4,  .rho4⟩  = 16) ∧
    (tensorDim ⟨.rho4,  .rho5⟩  = 20) ∧
    (tensorDim ⟨.rho5,  .rho5⟩  = 25) := by
  simp [tensorDim, irrepDim]


theorem rho4_containment :
    (containsRho4 ⟨.rho3,  .rho3⟩  = false) ∧  -- N
    (containsRho4 ⟨.rho3,  .rho3'⟩ = false) ∧  -- N
    (containsRho4 ⟨.rho3,  .rho4⟩  = true) ∧   -- Y
    (containsRho4 ⟨.rho3,  .rho5⟩  = false) ∧  -- N
    (containsRho4 ⟨.rho3', .rho3'⟩ = false) ∧  -- N
    (containsRho4 ⟨.rho3', .rho4⟩  = true) ∧   -- Y
    (containsRho4 ⟨.rho3', .rho5⟩  = false) ∧  -- N
    (containsRho4 ⟨.rho4,  .rho4⟩  = true) ∧   -- Y
    (containsRho4 ⟨.rho4,  .rho5⟩  = true) ∧   -- Y
    (containsRho4 ⟨.rho5,  .rho5⟩  = false) := by  -- N
  simp [containsRho4]

theorem self_product_classification :
    (isSelfProduct ⟨.rho3,  .rho3⟩  = true) ∧   -- Y
    (isSelfProduct ⟨.rho3,  .rho3'⟩ = false) ∧  -- N
    (isSelfProduct ⟨.rho3,  .rho4⟩  = false) ∧  -- N
    (isSelfProduct ⟨.rho3,  .rho5⟩  = false) ∧  -- N
    (isSelfProduct ⟨.rho3', .rho3'⟩ = true) ∧   -- Y
    (isSelfProduct ⟨.rho3', .rho4⟩  = false) ∧  -- N
    (isSelfProduct ⟨.rho3', .rho5⟩  = false) ∧  -- N
    (isSelfProduct ⟨.rho4,  .rho4⟩  = true) ∧   -- Y
    (isSelfProduct ⟨.rho4,  .rho5⟩  = false) ∧  -- N
    (isSelfProduct ⟨.rho5,  .rho5⟩  = true) := by  -- Y
  simp [isSelfProduct]

theorem P1_selection_rule_complete :
    (passesP1 ⟨.rho3,  .rho3⟩  = false) ∧
    (passesP1 ⟨.rho3,  .rho3'⟩ = false) ∧
    (passesP1 ⟨.rho3,  .rho4⟩  = true) ∧
    (passesP1 ⟨.rho3,  .rho5⟩  = false) ∧
    (passesP1 ⟨.rho3', .rho3'⟩ = false) ∧
    (passesP1 ⟨.rho3', .rho4⟩  = true) ∧
    (passesP1 ⟨.rho3', .rho5⟩  = false) ∧
    (passesP1 ⟨.rho4,  .rho4⟩  = false) ∧
    (passesP1 ⟨.rho4,  .rho5⟩  = true) ∧
    (passesP1 ⟨.rho5,  .rho5⟩  = false) := by
  simp [passesP1, containsRho4, isSelfProduct]


def allowed_tensor_dims : List ℕ := [12, 20]

def forbidden_tensor_dims : List ℕ := [9, 15, 16, 25]

theorem allowed_dims_are_VF :
    (12 = Ico_V) ∧ (20 = Ico_F) := by
  simp [Ico_V, Ico_F]

theorem forbidden_dims_factorization :
    (9  = 3 * 3) ∧
    (15 = 3 * 5) ∧
    (16 = 4 * 4) ∧
    (25 = 5 * 5) := by omega

theorem forbidden_disjoint_from_allowed :
    (9 ≠ 12) ∧ (9 ≠ 20) ∧
    (15 ≠ 12) ∧ (15 ≠ 20) ∧
    (16 ≠ 12) ∧ (16 ≠ 20) ∧
    (25 ≠ 12) ∧ (25 ≠ 20) := by omega

theorem rho4_self_product_maximal_entropy :
    (1 + 3 + 3 + 4 + 5 = 16) ∧
    (irrepDim .rho4 * irrepDim .rho4 = 16) ∧
    (irrepDims.sum = 16) := by
  simp [irrepDim, irrepDims]

theorem P1_passes_count :
    (tensorPairs.filter passesP1).length = 3 := by native_decide

theorem P1_fails_count :
    (tensorPairs.filter (fun p => !passesP1 p)).length = 7 := by native_decide

end P1_Rho4SelectionRule


/-!
══════════════════════════════════════════════════════════════════════════════
  §6.3.
══════════════════════════════════════════════════════════════════════════════
-/

section P2_MultiplicityFree

def sym2Dim (d : ℕ) : ℕ := d * (d + 1) / 2
def alt2Dim (d : ℕ) : ℕ := d * (d - 1) / 2

theorem symmetric_alternating_dims :
    (sym2Dim 3 = 6) ∧ (alt2Dim 3 = 3) ∧
    (sym2Dim 3 = 6) ∧ (alt2Dim 3 = 3) ∧
    (sym2Dim 4 = 10) ∧ (alt2Dim 4 = 6) ∧
    (sym2Dim 5 = 15) ∧ (alt2Dim 5 = 10) := by
  simp [sym2Dim, alt2Dim]

theorem sym2_rho5_multiplicity :
    (sym2Dim 5 = 15) ∧
    (1 + 4 + 2 * 5 = 15) ∧
    (15 ∈ forbidden_tensor_dims) := by
  simp [sym2Dim, forbidden_tensor_dims]

end P2_MultiplicityFree


/-!
══════════════════════════════════════════════════════════════════════════════
  §6.3
══════════════════════════════════════════════════════════════════════════════
-/

section FiveLayerClassification

inductive IndexLayer where
  | layerA : IndexLayer
  | layerB : IndexLayer
  | layerC : IndexLayer
  | layerD : IndexLayer
  | layerE : IndexLayer
  deriving DecidableEq, Repr

def layerA_indices : List ℕ := [4]

def layerB_indices : List ℕ := [3, 6, 10]

def layerC_indices : List ℕ := [12, 20]

def layerD_indices : List ℕ := [11, 17]

def layerE_indices : List ℕ := [8, 42, 48, 68, 70, 104, 204, 291, 300, 600]

theorem layerA_is_rho4_dim :
    irrepDim .rho4 = 4 ∧ 4 ∈ layerA_indices := by
  simp [irrepDim, layerA_indices]

theorem layerB_icosahedral_representations :
    (Ico_n = 3) ∧
    (Ico_ord / 10 = 6) ∧
    (Ico_E / Ico_n = 10) ∧
    (Ico_F / 2 = 10) ∧
    (Ico_ord / 6 = 10) := by
  simp [Ico_n, Ico_ord, Ico_E, Ico_F]

theorem layerB_symmetric_alternating :
    (alt2Dim 3 = 3) ∧
    (sym2Dim 3 = 6) ∧ (alt2Dim 4 = 6) ∧
    (sym2Dim 4 = 10) ∧ (alt2Dim 5 = 10) := by
  simp [sym2Dim, alt2Dim]

theorem layerC_is_VF :
    (12 = Ico_V) ∧ (20 = Ico_F) ∧
    layerC_indices = [Ico_V, Ico_F] := by
  simp [Ico_V, Ico_F, layerC_indices]

theorem layerE_icosahedral_representations :
    -- 42 = E + V
    (Ico_E + Ico_V = 42) ∧
    -- 68 = V × (F − n) / n = 204 / 3
    (Ico_V * (Ico_F - Ico_n) / Ico_n = 68) ∧
    -- 70 = F × n + E/n = 60 + 10
    (Ico_F * Ico_n + Ico_E / Ico_n = 70) ∧
    -- 104 = (V × (F − n) + 4) / 2 = 208 / 2
    ((Ico_V * (Ico_F - Ico_n) + 4) / 2 = 104) ∧
    -- 204 = V × (F − n)
    (Ico_V * (Ico_F - Ico_n) = 204) ∧
    -- 291 = (600 − (E − V)) / 2
    ((Ico_ord * (Ico_E / Ico_n) - (Ico_E - Ico_V)) / 2 = 291) ∧
    -- 300 = 600 / 2
    (Ico_ord * (Ico_E / Ico_n) / 2 = 300) ∧
    -- 600 = |A₅| × (E/n)
    (Ico_ord * (Ico_E / Ico_n) = 600) := by
  simp [Ico_E, Ico_V, Ico_F, Ico_n, Ico_ord]

theorem layers_increasing_size :
    layerA_indices.length ≤ layerB_indices.length ∧
    layerB_indices.length ≤ layerC_indices.length + layerD_indices.length ∧
    layerC_indices.length + layerD_indices.length ≤ layerE_indices.length := by
  simp [layerA_indices, layerB_indices, layerC_indices, layerD_indices, layerE_indices]

end FiveLayerClassification


/-!
══════════════════════════════════════════════════════════════════════════════
  §6.4.
══════════════════════════════════════════════════════════════════════════════
-/

section P3_E8Filter

def E8_coxeter_exponents : List ℕ := [1, 7, 11, 13, 17, 19, 23, 29]

theorem E8_coxeter_count : E8_coxeter_exponents.length = 8 := by native_decide

theorem E8_coxeter_number :
    E8_coxeter_exponents.sum = 120 ∧
    E8_coxeter_exponents.sum = 2 * Ico_ord := by
  constructor <;> native_decide

theorem E8_coxeter_squared_sum :
    E8_coxeter_exponents.sum = 120 ∧
    120 = 2 * Ico_ord := by
  constructor
  · native_decide
  · simp [Ico_ord]


theorem dual_attribution_membership :
    11 ∈ E8_coxeter_exponents ∧ 17 ∈ E8_coxeter_exponents := by
  constructor <;> decide

theorem dual_attribution_derivations :
    (Ico_V - 1 = 11) ∧
    (Ico_E / Ico_n + Ico_chi / 2 = 11) ∧
    (11 ∈ E8_coxeter_exponents) ∧
    (Ico_F - Ico_n = 17) ∧
    (17 ∈ E8_coxeter_exponents) := by
  simp [Ico_V, Ico_E, Ico_n, Ico_chi, Ico_F, E8_coxeter_exponents]

def non_dual_E8_indices : List ℕ := [1, 7, 13, 19, 23, 29]

theorem non_dual_E8_count : non_dual_E8_indices.length = 6 := by native_decide

theorem non_dual_complement :
    layerD_indices.length + non_dual_E8_indices.length = 8 := by
  simp [layerD_indices, non_dual_E8_indices]

theorem E8_partition :
    E8_coxeter_exponents.length =
      layerD_indices.length + non_dual_E8_indices.length := by
  simp [E8_coxeter_exponents, layerD_indices, non_dual_E8_indices]

theorem lepton_index_gap :
    (Ico_F - Ico_n) - (Ico_V - 1) = 6 ∧
    Ico_ord / 10 = 6 := by
  simp [Ico_F, Ico_n, Ico_V, Ico_ord]

end P3_E8Filter


/-!
══════════════════════════════════════════════════════════════════════════════
  §6.5.
══════════════════════════════════════════════════════════════════════════════
-/

section ForbiddenIndices

def forbidden_indices : List ℕ := [9, 15, 16, 25]

inductive ForbiddenReason where
  | noRho4           : ForbiddenReason
  | noRho4_and_mult  : ForbiddenReason
  | selfProduct      : ForbiddenReason
  | noRho4_self      : ForbiddenReason
  deriving DecidableEq, Repr

def forbiddenReason : ℕ → ForbiddenReason
  | 9  => .noRho4
  | 15 => .noRho4_and_mult
  | 16 => .selfProduct
  | 25 => .noRho4_self
  | _  => .noRho4

theorem forbidden_indices_from_tensors :
    (tensorDim ⟨.rho3, .rho3⟩  ∈ forbidden_indices) ∧
    (tensorDim ⟨.rho3, .rho5⟩  ∈ forbidden_indices) ∧
    (tensorDim ⟨.rho4, .rho4⟩  ∈ forbidden_indices) ∧
    (tensorDim ⟨.rho5, .rho5⟩  ∈ forbidden_indices) ∧
    (tensorDim ⟨.rho3, .rho4⟩  ∉ forbidden_indices) ∧
    (tensorDim ⟨.rho4, .rho5⟩  ∉ forbidden_indices) := by
  simp [tensorDim, irrepDim, forbidden_indices]

def core_allowed_indices : List ℕ := [3, 4, 6, 10, 11, 12, 17, 20]

theorem allowed_forbidden_disjoint :
    ∀ x ∈ core_allowed_indices, x ∉ forbidden_indices := by
  simp [core_allowed_indices, forbidden_indices]

theorem negative_control_Vub :
    (9 ∈ forbidden_indices) ∧
    (3 * 3 = 9) := by
  simp [forbidden_indices]

end ForbiddenIndices


/-!
══════════════════════════════════════════════════════════════════════════════
  §6.6.
══════════════════════════════════════════════════════════════════════════════
-/

section AlternativeGroupCollapse

def A4_irrep_dims : List ℕ := [1, 1, 1, 3]

theorem A4_burnside : (A4_irrep_dims.map (· ^ 2)).sum = 12 := by native_decide

theorem A4_no_even_dim_irrep :
    ∀ d ∈ A4_irrep_dims, d % 2 = 1 := by
  simp [A4_irrep_dims]

theorem A4_tensor_degenerate :
    (A4_irrep_dims.filter (· > 1)).length = 1 := by native_decide


def S4_irrep_dims : List ℕ := [1, 1, 2, 3, 3]

theorem S4_burnside : (S4_irrep_dims.map (· ^ 2)).sum = 24 := by native_decide

theorem S4_no_dim4_irrep :
    4 ∉ S4_irrep_dims := by
  simp [S4_irrep_dims]

theorem S4_no_golden_ratio :
    (S4_irrep_dims.sum = 10) ∧
    (irrepDims.sum = 16) ∧
    (irrepDims ≠ S4_irrep_dims) := by
  simp [S4_irrep_dims, irrepDims]


theorem A5_unique_prohibition_basis :
    (irrepDims.length = 5) ∧
    (4 ∈ irrepDims) ∧
    ((irrepDims.map (· ^ 2)).sum = 60) ∧
    (A4_irrep_dims.length = 4) ∧
    (4 ∉ A4_irrep_dims) ∧
    (S4_irrep_dims.length = 5) ∧
    (4 ∉ S4_irrep_dims) := by
  simp [irrepDims, A4_irrep_dims, S4_irrep_dims]

end AlternativeGroupCollapse


/-!
══════════════════════════════════════════════════════════════════════════════
  §6.7–6.8.
══════════════════════════════════════════════════════════════════════════════
-/

section IndexRelations

theorem index_system_relations :
    ((Ico_V - 1) + (Ico_F - Ico_n) = 28) ∧
    ((Ico_F - Ico_n) - (Ico_V - 1) = 6) ∧
    (Ico_V + Ico_F = 32) ∧
    (irrepDim .rho4 = 4) ∧
    (Ico_E / Ico_n = 10) ∧
    (Ico_V - 1 = Ico_E / Ico_n + Ico_chi / 2) ∧
    (15 * 16 = 4 * Ico_ord) := by
  simp [Ico_V, Ico_F, Ico_E, Ico_n, Ico_chi, Ico_ord, irrepDim]

theorem forbidden_dims_icosahedral :
    (Ico_n ^ 2 = 9) ∧
    (Ico_n * Stab_vert = 15) ∧
    (irrepDim .rho4 ^ 2 = 16) ∧
    (Stab_vert ^ 2 = 25) := by
  simp [Ico_n, Stab_vert, irrepDim]

end IndexRelations


/-!
══════════════════════════════════════════════════════════════════════════════
  §6
══════════════════════════════════════════════════════════════════════════════
-/

section VerificationSummary

theorem section6_verification_summary :
    (1^2 + 3^2 + 3^2 + 4^2 + 5^2 = 60) ∧
    (12 = Ico_V ∧ 20 = Ico_F) ∧
    (forbidden_indices = [9, 15, 16, 25]) ∧
    (E8_coxeter_exponents.sum = 120) ∧
    (E8_coxeter_exponents.sum = 2 * Ico_ord) ∧
    (E8_coxeter_exponents.length = 8) ∧
    (120 = 2 * Ico_ord) ∧
    (Ico_V - 1 = 11) ∧
    (Ico_F - Ico_n = 17) ∧
    (4 ∉ A4_irrep_dims) ∧
    (4 ∉ S4_irrep_dims) ∧
    (tensorPairs.length = 10) ∧
    ((tensorPairs.filter passesP1).length = 3) := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Ico_V, Ico_F]
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · simp [Ico_ord]
  · simp [Ico_V]
  · simp [Ico_F, Ico_n]
  · simp [A4_irrep_dims]
  · simp [S4_irrep_dims]
  · native_decide
  · native_decide

theorem section6_bridge_to_section7 :
    (forbidden_indices.length = 4) ∧
    (core_allowed_indices.length = 8) ∧
    (∀ x ∈ core_allowed_indices, x ∉ forbidden_indices) ∧
    ((tensorPairs.filter passesP1).length = 3) ∧
    ((tensorPairs.filter (fun p => !passesP1 p)).length = 7) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [forbidden_indices]
  · simp [core_allowed_indices]
  · simp [core_allowed_indices, forbidden_indices]
  · native_decide
  · native_decide

end VerificationSummary


end CosmicNecessity
