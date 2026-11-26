module
public import Swanepoel.PentagonConeCount
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace PentagonFaceBoundary
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} (P : PentagonFaceBoundary G F)
include P

def earDoubleArea (i : Fin 5) : ℝ :=
  -cross2 (carriedVector (P.dart i)) (carriedVector (P.dart (i+1)))

theorem adjacent_turn_inner_le_half (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht)
    (i : Fin 5) : inner ℝ (P.normal i) (P.normal (i+1))≤1/2 ∨
      inner ℝ (P.normal (i+1)) (P.normal (i+2))≤1/2 := by
  by_contra hn
  have h := not_or.mp hn
  have h1 : HalfOpen120Cone (P.normal (i+1)) (P.normal i) := Or.inl (by
    rw [real_inner_comm]
    exact lt_of_not_ge h.1)
  have h2 : HalfOpen120Cone (P.normal (i+1)) (P.normal (i+2)) := Or.inl (lt_of_not_ge h.2)
  have hs := HalfOpen120Cone.inner_gt_neg_half (P.normal_norm (i+1)) (P.normal_norm i)
    (P.normal_norm (i+2)) h1 h2
  linarith only [hs,P.normal_two_step_inner_le ht hF i]

theorem exists_two_large_ears (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht) :
    ∃ i : Fin 5, inner ℝ (P.normal i) (P.normal (i+1))≤1/2 ∧
      inner ℝ (P.normal (i+2)) (P.normal ((i+2)+1))≤1/2 := by
  let S := (Finset.univ : Finset (Fin 5)).filter
    (fun i => inner ℝ (P.normal i) (P.normal (i+1))≤1/2)
  have hfinite : ∀ T : Finset (Fin 5),(∀ i,i∈T ∨ i+1∈T) → ∃ i,i∈T ∧ i+2∈T := by decide
  obtain ⟨i,hi,hj⟩ := hfinite S (by
    intro i
    have h := P.adjacent_turn_inner_le_half ht hF i
    have hi : (i+1)+1=i+2 := by rw [add_assoc]; rfl
    simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and,hi] using h)
  exact ⟨i,(Finset.mem_filter.mp hi).2,(Finset.mem_filter.mp hj).2⟩

theorem earDoubleArea_lower (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht)
    (i : Fin 5) (hi : inner ℝ (P.normal i) (P.normal (i+1))≤1/2) :
    Real.sqrt 3/2≤P.earDoubleArea i := by
  have hlo := P.normal_adjacent_inner_gt_neg_half ht i
  have hcross := P.normal_clockwise_turn ht hF i
  have hsq := cross2_sq_add_inner_sq (P.normal i) (P.normal (i+1))
  rw [P.normal_norm,P.normal_norm] at hsq
  have hdot : (inner ℝ (P.normal i) (P.normal (i+1)))^2≤1/4 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hi) (by linarith only [hlo] :
      0 ≤ inner ℝ (P.normal i) (P.normal (i+1))+1/2)]
  have hroot := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have hnonneg := Real.sqrt_nonneg (3:ℝ)
  have hc : Real.sqrt 3/2≤ -cross2 (P.normal i) (P.normal (i+1)) := by
    nlinarith only [hroot,hnonneg,hcross,hsq,hdot]
  simpa only [earDoubleArea,normal,← rightNormalMap_carriedVector,rightNormalMap_cross] using hc

theorem faceSignedArea_eq_shoelace (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht) :
    G.faceSignedArea G.point F= -(∑ i : Fin 5,
      cross2 (G.point (P.vertex i)) (G.point (P.vertex (i+1))))/2 := by
  have hinc : G.faceIncidentDarts F=G.faceSourcePorts F := by
    ext e
    simp only [PennyGraph.faceIncidentDarts,PennyGraph.faceSourcePorts,Finset.mem_filter,
      Finset.mem_univ,true_and]
    exact ⟨fun he => ⟨G.spineSource_of_sourceFace_mem_defects ht e (he ▸ hF),he⟩,fun he => he.2⟩
  have hinj : Function.Injective P.dart := by
    intro i j h
    exact P.vertex_injective (congrArg (fun e : OrientedEdge G => e.val.1) h)
  rw [PennyGraph.faceSignedArea,hinc,← P.darts]
  change -(∑ e∈Finset.univ.image P.dart,cross2 (G.point e.val.1) (G.point e.val.2))/2= _
  rw [Finset.sum_image (fun i _ j _ h => hinj h)]
  rfl

theorem faceSignedArea_ear_decomposition (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht)
    (i : Fin 5) :
    2*G.faceSignedArea G.point F=P.earDoubleArea i+P.earDoubleArea (i+2)-
      cross2 (G.point (P.vertex (i+2))-G.point (P.vertex i))
        (G.point (P.vertex (i+4))-G.point (P.vertex i)) := by
  rw [P.faceSignedArea_eq_shoelace ht hF]
  fin_cases i <;> norm_num [earDoubleArea,dart,carriedVector,Fin.sum_univ_succ,cross2] <;> ring

theorem faceSignedArea_lower (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht) :
    Real.sqrt 3/2<G.faceSignedArea G.point F := by
  obtain ⟨i,hi,hj⟩ := P.exists_two_large_ears ht hF
  have h1 := P.earDoubleArea_lower ht hF i hi
  have h2 := P.earDoubleArea_lower ht hF (i+2) hj
  have hn0 : i+2≠i+4 := by fin_cases i <;> decide
  have hn1 : i+2≠(i+4)+1 := by fin_cases i <;> decide
  have hs := P.clockwise_edge_support ht hF (i+4) (i+2) hn0 hn1
  have hidx : (i+4)+1=i := by fin_cases i <;> decide
  rw [hidx] at hs
  have heq : cross2 (G.point (P.vertex i)-G.point (P.vertex (i+4)))
      (G.point (P.vertex (i+2))-G.point (P.vertex (i+4)))=
      cross2 (G.point (P.vertex (i+2))-G.point (P.vertex i))
        (G.point (P.vertex (i+4))-G.point (P.vertex i)) := by unfold cross2; simp; ring
  rw [heq] at hs
  linarith only [h1,h2,hs,P.faceSignedArea_ear_decomposition ht hF i]

end PentagonFaceBoundary

theorem PennyGraph.five_port_face_area_lower {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (hF : F∈G.defectPlaneFaces ht)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (hfive : (G.faceSourcePorts F).card=5) : Real.sqrt 3/2<G.faceSignedArea G.point F := by
  obtain ⟨P⟩ := G.five_port_face_boundary ht F hF hdegree hfive
  exact P.faceSignedArea_lower ht hF

end Swanepoel
