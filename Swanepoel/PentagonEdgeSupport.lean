module
public import Swanepoel.PentagonConvexity
public import Swanepoel.SupportedContactSegments
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

namespace PentagonFaceBoundary
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} (P : PentagonFaceBoundary G F)

theorem edge_strict_support (ht : G.TriangleFree) (i : Fin 5) :
    ∃ s : ℝ, s≠0 ∧ ∀ j : Fin 5, j≠i → j≠i+1 →
      0<s*cross2 (G.point (P.vertex (i+1))-G.point (P.vertex i))
        (G.point (P.vertex j)-G.point (P.vertex i)) := by
  let V (k : Fin 5) := P.vertex (i+k)
  have hne (k l : Fin 5) (h : k≠l) : V k≠V l :=
    fun heq => h (add_left_cancel (P.vertex_injective heq))
  obtain ⟨u,hu⟩ := P.vertex_strict_support ht (i+0)
  obtain ⟨v,hv⟩ := P.vertex_strict_support ht (i+1)
  have hU (k : Fin 5) (h : k≠0) : 0 < inner ℝ u (G.point (V k)-G.point (V 0)) :=
    hu (i+k) (fun heq => h (add_left_cancel heq))
  have hV (k : Fin 5) (h : k≠1) : 0 < inner ℝ v (G.point (V k)-G.point (V 1)) :=
    hv (i+k) (fun heq => h (add_left_cancel heq))
  have h01 : G.graph.Adj (V 0) (V 1) := by simpa only [V,add_zero] using P.contact i
  have h23 : G.graph.Adj (V 2) (V 3) := by
    simpa only [V,add_assoc,show (2:Fin 5)+1=3 by decide] using P.contact (i+2)
  have h34 : G.graph.Adj (V 3) (V 4) := by
    simpa only [V,add_assoc,show (3:Fin 5)+1=4 by decide] using P.contact (i+3)
  let cross (k : Fin 5) := cross2 (G.point (V 1)-G.point (V 0)) (G.point (V k)-G.point (V 0))
  have hc (k : Fin 5) (hk0 : k≠0) (hk1 : k≠1) : cross k≠0 :=
    G.supported_contact_cross_ne_zero (V 0) (V 1) (V k) h01 (hne k 0 hk0) u v
      (hU 1 (by decide)) (hV 0 (by decide)) (hU k hk0) (hV k hk1)
  have hp23 : 0<cross 2*cross 3 := by
    have h := G.supported_nonincident_edge_cross_nonneg (V 0) (V 1) (V 2) (V 3) h01 h23
      (hne 0 2 (by decide)) (hne 0 3 (by decide)) (hne 1 2 (by decide)) (hne 1 3 (by decide)) u v
      (hU 1 (by decide)) (hV 0 (by decide)) (hU 2 (by decide)) (hU 3 (by decide))
      (hV 2 (by decide)) (hV 3 (by decide))
    exact lt_of_le_of_ne h (Ne.symm (mul_ne_zero (hc 2 (by decide) (by decide)) (hc 3 (by decide) (by decide))))
  have hp34 : 0<cross 3*cross 4 := by
    have h := G.supported_nonincident_edge_cross_nonneg (V 0) (V 1) (V 3) (V 4) h01 h34
      (hne 0 3 (by decide)) (hne 0 4 (by decide)) (hne 1 3 (by decide)) (hne 1 4 (by decide)) u v
      (hU 1 (by decide)) (hV 0 (by decide)) (hU 3 (by decide)) (hU 4 (by decide))
      (hV 3 (by decide)) (hV 4 (by decide))
    exact lt_of_le_of_ne h (Ne.symm (mul_ne_zero (hc 3 (by decide) (by decide)) (hc 4 (by decide) (by decide))))
  have hp24 : 0<cross 2*cross 4 := by
    rcases mul_pos_iff.mp hp23 with h | h
    · have hk := (mul_pos_iff.mp hp34).resolve_right (fun hk => h.2.not_gt hk.1)
      exact mul_pos h.1 hk.2
    · have hk := (mul_pos_iff.mp hp34).resolve_left (fun hk => h.2.not_gt hk.1)
      exact mul_pos_of_neg_of_neg h.1 hk.2
  refine ⟨cross 2,hc 2 (by decide) (by decide),?_⟩
  intro j hj0 hj1
  have hj : j=i+2 ∨ j=i+3 ∨ j=i+4 := by
    fin_cases i <;> fin_cases j <;> norm_num at *
  rcases hj with rfl | rfl | rfl
  · simpa only [cross,V,add_zero] using mul_self_pos.mpr (hc 2 (by decide) (by decide))
  · simpa only [cross,V,add_zero] using hp23
  · simpa only [cross,V,add_zero] using hp24

end PentagonFaceBoundary
end Swanepoel
