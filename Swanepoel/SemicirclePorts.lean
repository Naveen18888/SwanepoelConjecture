module
public import Swanepoel.DefectBoundary
public import Swanepoel.TrackClassification
public import Mathlib.Algebra.BigOperators.Fin
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def rightNormalMap : Plane →ₗ[ℝ] Plane where
  toFun u := -quarterTurn u
  map_add' u v := by
    ext i
    fin_cases i <;> simp [quarterTurn, add_comm]
  map_smul' a u := by
    ext i
    fin_cases i <;> simp [quarterTurn]

theorem rightNormalMap_norm (u : Plane) : ‖rightNormalMap u‖ = ‖u‖ := by
  exact (norm_neg _).trans (quarterTurn_norm u)

theorem rightNormalMap_carriedVector {n : ℕ} {G : PennyGraph n}
    (e : OrientedEdge G) : rightNormalMap (carriedVector e) = sourceNormal e := rfl

theorem rightNormalMap_cross (u w : Plane) :
    cross2 (rightNormalMap u) (rightNormalMap w) = cross2 u w := by
  change cross2 (-quarterTurn u) (-quarterTurn w) = cross2 u w
  simp [quarterTurn, cross2]
  ring

theorem polygon_edge_sum {k : ℕ} (p : Fin (k+1) → Plane) :
    (∑ i : Fin k, (p i.succ-p i.castSucc)) = p (Fin.last k)-p 0 := by
  rw [Finset.sum_sub_distrib]
  have hfirst := Fin.sum_univ_succ p
  have hlast := Fin.sum_univ_castSucc p
  calc
    _ = ((p 0 + ∑ i : Fin k, p i.succ) -
      ((∑ i : Fin k, p i.castSucc) + p (Fin.last k))) +
        (p (Fin.last k)-p 0) := by abel
    _ = p (Fin.last k)-p 0 := by rw [← hfirst, ← hlast]; abel

theorem polygon_normal_sum {k : ℕ} (p : Fin (k+1) → Plane)
    (hclosed : p (Fin.last k) = p 0) :
    (∑ i : Fin k, rightNormalMap (p i.succ-p i.castSucc)) = 0 := by
  rw [← map_sum, polygon_edge_sum, hclosed, sub_self, map_zero]

theorem contact_chain_sourceNormal_sum {n k : ℕ} (G : PennyGraph n)
    (vertices : Fin (k+1) → Fin n) (edges : Fin k → OrientedEdge G)
    (hstart : ∀ i, (edges i).val.1 = vertices i.castSucc)
    (hend : ∀ i, (edges i).val.2 = vertices i.succ)
    (hclosed : vertices (Fin.last k) = vertices 0) :
    (∑ i : Fin k, sourceNormal (edges i)) = 0 := by
  have h := polygon_normal_sum (fun i => G.point (vertices i)) (congrArg G.point hclosed)
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [← rightNormalMap_carriedVector, carriedVector, hstart, hend]

theorem balanced_normals_positive {ι : Type*} [Fintype ι]
    (normal : ι → Plane) (hsum : ∑ i, normal i = 0) (v : Plane)
    (hnonzero : ∃ i, inner ℝ v (normal i) ≠ 0) :
    ∃ i, 0 < inner ℝ v (normal i) := by
  by_contra hn
  have hle (i : ι) : inner ℝ v (normal i) ≤ 0 := by
    by_contra hi
    exact hn ⟨i, lt_of_not_ge hi⟩
  have hprojection : ∑ i, inner ℝ v (normal i) = 0 := by
    rw [← inner_sum, hsum, inner_zero_right]
  have hall := (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => hle i)).mp hprojection
  obtain ⟨i, hi⟩ := hnonzero
  exact hi (hall i (Finset.mem_univ _))

theorem balanced_normals_meet_every_semicircle {ι : Type*} [Fintype ι]
    (normal : ι → Plane) (hsum : ∑ i, normal i = 0)
    (a b : ι) (hind : cross2 (normal a) (normal b) ≠ 0)
    (v : Plane) (hv : v ≠ 0) :
    ∃ i, 0 < inner ℝ v (normal i) := by
  apply balanced_normals_positive normal hsum v
  by_contra hn
  have hzero (i : ι) : inner ℝ v (normal i) = 0 := by
    by_contra hi
    exact hn ⟨i, hi⟩
  have hrec := cramer_reconstruct (normal a) (normal b) v hind
  have hself : inner ℝ v v = 0 := by
    calc
      _ = inner ℝ v ((cross2 v (normal b)/cross2 (normal a) (normal b)) • normal a +
          (cross2 (normal a) v/cross2 (normal a) (normal b)) • normal b) :=
        congrArg (inner ℝ v) hrec.symm
      _ = 0 := by rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
        hzero a, hzero b, mul_zero, mul_zero, add_zero]
  exact hv (inner_self_eq_zero.mp hself)

theorem PennyGraph.closed_defect_boundary_meets_semicircle {n k : ℕ}
    (G : PennyGraph n) (ht : G.TriangleFree) (F : PlaneFace G)
    (hF : F ∈ G.defectPlaneFaces ht)
    (vertices : Fin (k+1) → Fin n) (edges : Fin k → OrientedEdge G)
    (hstart : ∀ i, (edges i).val.1 = vertices i.castSucc)
    (hend : ∀ i, (edges i).val.2 = vertices i.succ)
    (hclosed : vertices (Fin.last k) = vertices 0)
    (hface : ∀ i, G.sourceFace (edges i) = F)
    (a b : Fin k) (hind : cross2 (carriedVector (edges a)) (carriedVector (edges b)) ≠ 0)
    (v : Plane) (hv : v ≠ 0) :
    ∃ e ∈ G.faceSourcePorts F, 0 < inner ℝ v (sourceNormal e) := by
  have hnind : cross2 (sourceNormal (edges a)) (sourceNormal (edges b)) ≠ 0 := by
    simpa only [← rightNormalMap_carriedVector, rightNormalMap_cross] using hind
  obtain ⟨i, hi⟩ := balanced_normals_meet_every_semicircle
    (fun i => sourceNormal (edges i))
    (contact_chain_sourceNormal_sum G vertices edges hstart hend hclosed) a b hnind v hv
  refine ⟨edges i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hface i⟩, hi⟩
  apply G.spineSource_of_sourceFace_mem_defects ht
  rw [hface i]
  exact hF

theorem unique_positive_normal_reduction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (normal : ι → Plane) (hsum : ∑ i, normal i = 0)
    (hunit : ∀ i, ‖normal i‖ = 1) (v : Plane) (a : ι)
    (hunique : ∀ i, 0 < inner ℝ v (normal i) → i = a) :
    (∀ i ∈ (Finset.univ.erase a : Finset ι), inner ℝ v (normal i) ≤ 0) ∧
      (∑ i ∈ (Finset.univ.erase a : Finset ι), normal i) = -normal a ∧
      ‖∑ i ∈ (Finset.univ.erase a : Finset ι), normal i‖ = 1 := by
  have hsum' : (∑ i ∈ (Finset.univ.erase a : Finset ι), normal i) = -normal a := by
    have h := Finset.sum_erase_add (s := Finset.univ) normal (Finset.mem_univ a)
    rw [hsum] at h
    exact eq_neg_of_add_eq_zero_left h
  refine ⟨?_, hsum', ?_⟩
  · intro i hi
    by_contra hpos
    have heq := hunique i (lt_of_not_ge hpos)
    exact (Finset.mem_erase.mp hi).1 heq
  · rw [hsum', norm_neg, hunit a]

def semicircleCancellationSteps : Fin 5 → Plane :=
  ![EuclideanSpace.single 1 1, EuclideanSpace.single 1 1,
    EuclideanSpace.single 0 1, -EuclideanSpace.single 1 1, -EuclideanSpace.single 1 1]

theorem semicircle_cancellation_example :
    (∀ i, ‖semicircleCancellationSteps i‖ = 1) ∧
    (∀ i, 0 ≤ inner ℝ (EuclideanSpace.single 0 (1 : ℝ))
      (semicircleCancellationSteps i)) ∧
    ‖∑ i, semicircleCancellationSteps i‖ = 1 ∧
    (∀ i : Fin 4, 1 < ‖semicircleCancellationSteps i.castSucc +
      semicircleCancellationSteps i.succ‖) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [semicircleCancellationSteps]
  · intro i
    fin_cases i <;> simp [semicircleCancellationSteps, PiLp.inner_apply]
  · have hs : (∑ i, semicircleCancellationSteps i) = EuclideanSpace.single 0 (1 : ℝ) := by
      ext i
      fin_cases i <;> norm_num [semicircleCancellationSteps, Fin.sum_univ_succ]
    rw [hs]
    simp
  · intro i
    have hn := norm_nonneg (semicircleCancellationSteps i.castSucc +
      semicircleCancellationSteps i.succ)
    have hs : ‖semicircleCancellationSteps i.castSucc +
        semicircleCancellationSteps i.succ‖ ^ 2 =
        if i.val = 0 ∨ i.val = 3 then 4 else 2 := by
      fin_cases i <;> norm_num [semicircleCancellationSteps,
        EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    split_ifs at hs <;> nlinarith

end Swanepoel
