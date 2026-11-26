module
public import Swanepoel.BankPortProjection
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem balanced_unit_120_cone_count {ι : Type*} [DecidableEq ι]
    (Q : Finset ι) (normal : ι→Plane) (hnorm : ∀ i∈Q,‖normal i‖=1)
    (hsum : ∑ i∈Q,normal i=0) (b : Plane) (hb : ‖b‖=1) (hQ : 6≤Q.card) :
    (Q.filter (fun i => (1/2:ℝ) < inner ℝ b (normal i))).card+3≤Q.card := by
  let P := Q.filter (fun i => (1/2:ℝ) < inner ℝ b (normal i))
  by_contra hn
  change ¬P.card+3≤Q.card at hn
  have hp : 0<P.card := by omega
  have hP : P.Nonempty := Finset.card_pos.mp hp
  let T := P.image (fun i => inner ℝ b (normal i))
  have hT : T.Nonempty := hP.image _
  let α := T.min' hT
  have hα : (1/2:ℝ)<α := by
    obtain ⟨i,hi,heq⟩ := Finset.mem_image.mp (Finset.min'_mem T hT)
    change (1/2:ℝ)<T.min' hT
    rw [← heq]
    exact (Finset.mem_filter.mp hi).2
  have hmin : ∀ i∈P,α ≤ inner ℝ b (normal i) := by
    intro i hi
    exact Finset.min'_le T _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
  have hproj := balanced_unit_subset_projection Q P (Finset.filter_subset _ _) normal b α hb hnorm hsum hmin
  have hpR : (0:ℝ)<P.card := by exact_mod_cast hp
  have hcount : (Q.card : ℝ)≤(P.card : ℝ)+2 := by exact_mod_cast (show Q.card≤P.card+2 by omega)
  have hmR : (6:ℝ)≤Q.card := by exact_mod_cast hQ
  have hstrict := mul_pos (sub_pos.mpr hα) hpR
  nlinarith

theorem PennyGraph.large_defect_open_120_cone_count {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (hF : F∈G.defectPlaneFaces ht)
    (hsize : 6≤(G.faceSourcePorts F).card) (b : Plane) (hb : ‖b‖=1) :
    ((G.faceSourcePorts F).filter (fun e => (1/2:ℝ) < inner ℝ b (sourceNormal e))).card+3≤
      (G.faceSourcePorts F).card :=
  balanced_unit_120_cone_count _ sourceNormal (fun e _ => sourceNormal_norm e)
    (G.defect_all_source_normals_sum ht F hF) b hb hsize

end Swanepoel
