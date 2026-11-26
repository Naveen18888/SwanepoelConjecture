module
public import Swanepoel.FaceCycleArea
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem PennyGraph.boundary_darts_area_bound {n : ℕ} (G : PennyGraph n) (P : Fin n→Plane)
    (hunit : ∀ e : OrientedEdge G,P e.val.2-P e.val.1=0 ∨ ‖P e.val.2-P e.val.1‖=1)
    (S : Finset (OrientedEdge G)) (hS : ∀ e∈S,G.faceBoundarySuccessor e∈S) :
    |(∑ e∈S,cross2 (P e.val.1) (P e.val.2))/2|≤
      (∑ e∈S,‖P e.val.2-P e.val.1‖)^2/(4*Real.pi) := by
  have hAll : ∀ m : ℕ, ∀ T : Finset (OrientedEdge G), T.card=m →
      (∀ e∈T,G.faceBoundarySuccessor e∈T) →
      |(∑ e∈T,cross2 (P e.val.1) (P e.val.2))/2|≤
        (∑ e∈T,‖P e.val.2-P e.val.1‖)^2/(4*Real.pi) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro T hcard hT
      by_cases hempty : T=∅
      · simp [hempty]
      · obtain ⟨e,he⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
        obtain ⟨C⟩ := G.minimal_face_boundary_cycle (G.sourceFace e) e rfl
        have hsub := C.dartSet_subset_of_successor_closed T he hT
        have hrest : ∀ f∈T\C.dartSet,G.faceBoundarySuccessor f∈T\C.dartSet := by
          intro f hf
          have hf' := Finset.mem_sdiff.mp hf
          exact Finset.mem_sdiff.mpr ⟨hT f hf'.1,fun hn => hf'.2 ((C.dartSet_successor_iff f).mp hn)⟩
        have hless : (T\C.dartSet).card<m := by
          have hc := Finset.card_sdiff_add_card_eq_card hsub
          have hp : 0<C.dartSet.card := Finset.card_pos.mpr ⟨e,C.dartSet_mem_initial⟩
          omega
        have hrec := ih (T\C.dartSet).card hless (T\C.dartSet) rfl hrest
        have hcycle := C.dartSet_area_bound P hunit
        let a := (∑ f∈C.dartSet,cross2 (P f.val.1) (P f.val.2))/2
        let b := (∑ f∈T\C.dartSet,cross2 (P f.val.1) (P f.val.2))/2
        let L := ∑ f∈C.dartSet,‖P f.val.2-P f.val.1‖
        let M := ∑ f∈T\C.dartSet,‖P f.val.2-P f.val.1‖
        have hA : (∑ f∈T,cross2 (P f.val.1) (P f.val.2))/2=a+b := by
          have hh := Finset.sum_sdiff (f := fun f => cross2 (P f.val.1) (P f.val.2)) hsub
          dsimp [a,b]
          linarith
        have hL : (∑ f∈T,‖P f.val.2-P f.val.1‖)=L+M := by
          have hh := Finset.sum_sdiff (f := fun f => ‖P f.val.2-P f.val.1‖) hsub
          dsimp [L,M]
          linarith
        have hLn : 0≤L := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
        have hMn : 0≤M := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
        rw [hA,hL]
        calc
          |a+b| ≤ |a|+|b| := abs_add_le _ _
          _ ≤ L^2/(4*Real.pi)+M^2/(4*Real.pi) := add_le_add hcycle hrec
          _ ≤ (L+M)^2/(4*Real.pi) := by
            rw [← add_div]
            apply (div_le_div_iff_of_pos_right (by positivity : (0:ℝ)<4*Real.pi)).mpr
            nlinarith [mul_nonneg hLn hMn]
  exact hAll S.card S rfl hS

theorem PennyGraph.face_signed_area_perimeter_bound {n : ℕ} (G : PennyGraph n)
    (P : Fin n→Plane)
    (hunit : ∀ e : OrientedEdge G,P e.val.2-P e.val.1=0 ∨ ‖P e.val.2-P e.val.1‖=1)
    (F : PlaneFace G) :
    |G.faceSignedArea P F|≤(∑ e∈G.faceIncidentDarts F,‖P e.val.2-P e.val.1‖)^2/(4*Real.pi) := by
  have hS : ∀ e∈G.faceIncidentDarts F,G.faceBoundarySuccessor e∈G.faceIncidentDarts F := by
    intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (G.faceBoundarySuccessor_face e).trans (Finset.mem_filter.mp he).2⟩
  simpa only [faceSignedArea,neg_div,abs_neg] using G.boundary_darts_area_bound P hunit _ hS

end Swanepoel
