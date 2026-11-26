module
public import Swanepoel.VerticalSliceGeometry
public import Swanepoel.FiniteJumpFill
@[expose] public section

noncomputable section
namespace Swanepoel
open Filter
open scoped Topology BigOperators
attribute [local instance] Classical.propDecidable

def faceIndicatorValue {n : ℕ} {G : PennyGraph n} (F H : PlaneFace G) : ℝ := if H=F then 1 else 0

def PennyGraph.faceSliceValue {n : ℕ} (G : PennyGraph n) (F : PlaneFace G) (x y : ℝ) : ℝ :=
  if cartPoint x y∈F.val then 1 else 0

theorem PennyGraph.faceSliceValue_eq_of_mem {n : ℕ} (G : PennyGraph n)
    (F H : PlaneFace G) (x y : ℝ) (hy : cartPoint x y∈H.val) :
    G.faceSliceValue F x y=faceIndicatorValue F H := by
  have hiff : cartPoint x y∈F.val ↔ H=F := by
    constructor
    · intro hF
      exact Subtype.ext ((H.property.eq_component hy).trans (F.property.eq_component hF).symm)
    · intro h
      rwa [← h]
  simp only [PennyGraph.faceSliceValue,faceIndicatorValue,hiff]

theorem PennyGraph.faceSliceValue_locally_constant {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) (x c : ℝ) (hc : cartPoint x c∉G.drawing) :
    ∀ᶠ y in 𝓝 c,G.faceSliceValue F x y=G.faceSliceValue F x c := by
  let H : PlaneFace G := ⟨connectedComponentIn G.drawingᶜ (cartPoint x c),⟨cartPoint x c,hc,rfl⟩⟩
  have hz : cartPoint x c∈H.val := mem_connectedComponentIn hc
  have hN : ∀ᶠ y in 𝓝 c,cartPoint x y∈H.val :=
    (continuous_cartPoint x).continuousAt.eventually (H.property.isOpen.mem_nhds hz)
  filter_upwards [hN] with y hy
  rw [G.faceSliceValue_eq_of_mem F H x y hy,G.faceSliceValue_eq_of_mem F H x c hz]

def ContactEdge.sliceLowerFace {n : ℕ} {G : PennyGraph n} (e : ContactEdge G) : PlaneFace G :=
  if 0<G.point e.val.2 0-G.point e.val.1 0 then G.sourceFace e.forwardEdge
  else G.sourceFace (reverseEdge e.forwardEdge)

def ContactEdge.sliceUpperFace {n : ℕ} {G : PennyGraph n} (e : ContactEdge G) : PlaneFace G :=
  if 0<G.point e.val.2 0-G.point e.val.1 0 then G.sourceFace (reverseEdge e.forwardEdge)
  else G.sourceFace e.forwardEdge

theorem PennyGraph.faceSliceValue_local_jump {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) (x : ℝ) (e : SliceEdge G x) :
    ∀ᶠ y in 𝓝 (e.val.sliceHeight x),y≠e.val.sliceHeight x →
      G.faceSliceValue F x y=if y<e.val.sliceHeight x then
        faceIndicatorValue F e.val.sliceLowerFace else faceIndicatorValue F e.val.sliceUpperFace := by
  have he := e.val.sliceParameter_bounds e.property
  obtain ⟨r,hr,hR⟩ := G.right_face_halfBall_at e.val.forwardEdge he.2.1 he.2.2
  obtain ⟨s,hs,hL⟩ := G.left_face_halfBall_at e.val.forwardEdge he.2.1 he.2.2
  have hε : 0<min r s := lt_min hr hs
  filter_upwards [Metric.ball_mem_nhds (e.val.sliceHeight x) hε] with y hy
  intro hyne
  have hdist : |y-e.val.sliceHeight x|<min r s := hy
  have hballR : cartPoint x y∈Metric.ball
      (G.edgePoint e.val.val.1 e.val.val.2 (e.val.sliceParameter x)) r := by
    rw [Metric.mem_ball,e.val.edgePoint_slice e.property,cartPoint_dist]
    exact hdist.trans_le (min_le_left _ _)
  have hballL : cartPoint x y∈Metric.ball
      (G.edgePoint e.val.val.1 e.val.val.2 (e.val.sliceParameter x)) s := by
    rw [Metric.mem_ball,e.val.edgePoint_slice e.property,cartPoint_dist]
    exact hdist.trans_le (min_le_right _ _)
  have right (h : (G.point e.val.val.2 0-G.point e.val.val.1 0)*(y-e.val.sliceHeight x)<0) :
      G.faceSliceValue F x y=faceIndicatorValue F (G.sourceFace e.val.forwardEdge) := by
    apply G.faceSliceValue_eq_of_mem F (G.sourceFace e.val.forwardEdge) x y
    apply hR ⟨hballR,?_⟩
    change cross2 (carriedVector e.val.forwardEdge) (cartPoint x y)<
      cross2 (carriedVector e.val.forwardEdge) (G.edgePoint e.val.val.1 e.val.val.2 (e.val.sliceParameter x))
    rw [e.val.edgePoint_slice e.property]
    apply sub_neg.mp
    rwa [e.val.slice_cross_difference]
  have left (h : 0<(G.point e.val.val.2 0-G.point e.val.val.1 0)*(y-e.val.sliceHeight x)) :
      G.faceSliceValue F x y=faceIndicatorValue F (G.sourceFace (reverseEdge e.val.forwardEdge)) := by
    apply G.faceSliceValue_eq_of_mem F (G.sourceFace (reverseEdge e.val.forwardEdge)) x y
    apply hL ⟨hballL,?_⟩
    change cross2 (carriedVector e.val.forwardEdge) (G.edgePoint e.val.val.1 e.val.val.2 (e.val.sliceParameter x))<
      cross2 (carriedVector e.val.forwardEdge) (cartPoint x y)
    rw [e.val.edgePoint_slice e.property]
    apply sub_pos.mp
    rwa [e.val.slice_cross_difference]
  by_cases hd : 0<G.point e.val.val.2 0-G.point e.val.val.1 0
  · by_cases hylo : y<e.val.sliceHeight x
    · rw [ite_eq_left hylo]
      simpa only [ContactEdge.sliceLowerFace,ite_eq_left hd] using
        right (mul_neg_of_pos_of_neg hd (sub_neg.mpr hylo))
    · rw [ite_eq_right hylo]
      have hypos : 0<y-e.val.sliceHeight x := sub_pos.mpr
        (lt_of_le_of_ne (le_of_not_gt hylo) hyne.symm)
      simpa only [ContactEdge.sliceUpperFace,ite_eq_left hd] using left (mul_pos hd hypos)
  · have hdneg : G.point e.val.val.2 0-G.point e.val.val.1 0<0 := lt_of_le_of_ne (le_of_not_gt hd) he.1
    by_cases hylo : y<e.val.sliceHeight x
    · rw [ite_eq_left hylo]
      simpa only [ContactEdge.sliceLowerFace,ite_eq_right hd] using
        left (mul_pos_of_neg_of_neg hdneg (sub_neg.mpr hylo))
    · rw [ite_eq_right hylo]
      have hypos : 0<y-e.val.sliceHeight x := sub_pos.mpr
        (lt_of_le_of_ne (le_of_not_gt hylo) hyne.symm)
      simpa only [ContactEdge.sliceUpperFace,ite_eq_right hd] using
        right (mul_neg_of_neg_of_pos hdneg hypos)

theorem PennyGraph.faceSliceValue_reconstruction {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) (hF : Bornology.IsBounded F.val)
    (x : ℝ) (hx : ∀ v : Fin n,x≠G.point v 0) :
    ∀ y,(∀ e : SliceEdge G x,y≠e.val.sliceHeight x) →
      G.faceSliceValue F x y=finiteJumpSum (fun e : SliceEdge G x => e.val.sliceHeight x)
        (fun e => faceIndicatorValue F e.val.sliceLowerFace-faceIndicatorValue F e.val.sliceUpperFace) y := by
  let height (e : SliceEdge G x) := e.val.sliceHeight x
  obtain ⟨R,hR⟩ := isBounded_iff_forall_norm_le.mp hF
  obtain ⟨M,hM⟩ := (Set.finite_range height).bddAbove
  let a := max R M+1
  have ha (e : SliceEdge G x) : height e<a := by
    have hh := hM ⟨e,rfl⟩
    have hm := le_max_right R M
    dsimp [a]
    linarith only [hh,hm]
  have hfa : G.faceSliceValue F x a=0 := by
    apply ite_eq_right
    intro hz
    have hnorm := hR (cartPoint x a) hz
    have hcoord := PiLp.norm_apply_le (cartPoint x a) (1:Fin 2)
    change ‖a‖≤‖cartPoint x a‖ at hcoord
    rw [Real.norm_eq_abs] at hcoord
    have haR : R<a := by dsimp [a]; linarith only [le_max_left R M]
    linarith only [hnorm,hcoord,le_abs_self a,haR]
  apply finite_jump_reconstruction_off height
    (fun e => faceIndicatorValue F e.val.sliceLowerFace)
    (fun e => faceIndicatorValue F e.val.sliceUpperFace) (G.sliceHeight_injective x)
    (G.faceSliceValue F x) ?_ (G.faceSliceValue_local_jump F x) a ha hfa
  intro c hc
  apply G.faceSliceValue_locally_constant F x c
  intro hdraw
  obtain ⟨e,he⟩ := (G.cartPoint_mem_drawing_iff x hx c).mp hdraw
  exact hc e he

end Swanepoel
