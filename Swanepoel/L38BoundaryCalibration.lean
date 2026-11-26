module
public import Swanepoel.L38AnisotropicFrame
public import Swanepoel.FaceAreaIsoperimetry
public import Mathlib.GroupTheory.Perm.Fin
@[expose] public section
set_option autoImplicit false

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem l38_finRotate_cycle {k : ℕ} (hk : 0<k) : (finRotate k).IsCycleOn Set.univ := by
  by_cases hk1 : k=1
  · subst k
    exact Equiv.Perm.isCycleOn_of_subsingleton _ _
  · have hk2 : 2≤k := by omega
    have hfull : {i : Fin k | finRotate k i≠i}=Set.univ := by
      ext i
      simp only [Set.mem_ofPred_eq,Set.mem_univ,iff_true]
      apply Equiv.Perm.mem_support.mp
      rw [support_finRotate_of_le hk2]
      exact Finset.mem_univ i
    simpa only [hfull] using (isCycle_finRotate_of_le hk2).isCycleOn

theorem l38_rotate_closed_vertex {α : Type*} {k : ℕ} (hk : 0<k)
    (p : Fin (k+1)→α) (hclosed : p (Fin.last k)=p 0) (i : Fin k) :
    p (finRotate k i).castSucc=p i.succ := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
  by_cases hi : i.val<j
  · have hrot : finRotate (j+1) i=⟨i.val+1,Nat.succ_lt_succ hi⟩ := finRotate_of_lt hi
    rw [hrot]
    rfl
  · have hlast : i=Fin.last j := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
    rw [hlast,finRotate_last]
    exact hclosed.symm

def l38BoundaryCost {ι : Type*} (bank : ι→Prop) (l : ι→ℝ) (i : ι) : ℝ :=
  if bank i then l i/3 else l i

theorem l38BoundaryCost_nonneg {ι : Type*} (bank : ι→Prop) (l : ι→ℝ) (i : ι)
    (hl : 0≤l i) : 0≤l38BoundaryCost bank l i := by unfold l38BoundaryCost; split_ifs <;> positivity

theorem l38BoundaryCost_sum {ι : Type*} (S : Finset ι) (bank : ι→Prop) (l : ι→ℝ) :
    (∑ i∈S,l38BoundaryCost bank l i)=(∑ i∈S,l i)-(2/3:ℝ)*(∑ i∈S,if bank i then l i else 0) := by
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold l38BoundaryCost
  split_ifs <;> ring

namespace FaceBoundaryCycle
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} {initial : OrientedEdge G}
    (C : FaceBoundaryCycle G F initial)

theorem dartSet_bank_area_bound (P : Fin n→Plane) (u : Plane) (hu : ‖u‖=1)
    (bank : OrientedEdge G→Prop) (l : OrientedEdge G→ℝ)
    (hl : ∀ e,0≤l e)
    (hdisp : ∀ e : OrientedEdge G,P e.val.2-P e.val.1=l e • carriedVector e)
    (hbank : ∀ e∈C.dartSet,bank e → Real.sqrt 3/2≤ inner ℝ u (sourceNormal e)) :
    4*l38CertificateArea*((∑ e∈C.dartSet,cross2 (P e.val.1) (P e.val.2))/2)≤
      (∑ e∈C.dartSet,l38BoundaryCost bank l e)^2 := by
  let : Nonempty (Fin C.length) := ⟨⟨0,C.length_pos⟩⟩
  let p (i : Fin C.length) := P (C.vertex i.castSucc)
  have hnext (i : Fin C.length) : p (finRotate C.length i)=P (C.vertex i.succ) :=
    l38_rotate_closed_vertex C.length_pos (fun j => P (C.vertex j))
      (by rw [C.vertex_closes]) i
  have hedge (i : Fin C.length) : p (finRotate C.length i)-p i=
      l (C.edge i.castSucc) • carriedVector (C.edge i.castSucc) := by
    rw [hnext]
    simpa only [p,C.edge_start,C.edge_end] using hdisp (C.edge i.castSucc)
  have hc := l38_oriented_bank_walk_area_bound (finRotate C.length)
    (l38_finRotate_cycle C.length_pos) p u hu
    (fun i => bank (C.edge i.castSucc)) (fun i => l (C.edge i.castSucc))
    (fun i => carriedVector (C.edge i.castSucc)) (fun i => hl _) (fun i => carriedVector_norm _) hedge
    (fun i hb => by
      rw [rightNormalMap_carriedVector]
      exact hbank _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) hb)
  have harea : cyclicSignedArea (finRotate C.length) p=
      (∑ e∈C.dartSet,cross2 (P e.val.1) (P e.val.2))/2 := by
    unfold cyclicSignedArea cyclicDoubleArea
    simp_rw [hnext]
    simp only [dartSet,Finset.sum_image (fun i _ j _ h => C.edge_injective h),
      p,C.edge_start,C.edge_end]
  have hcost : (∑ e∈C.dartSet,l38BoundaryCost bank l e)=
      ∑ i : Fin C.length,if bank (C.edge i.castSucc) then l (C.edge i.castSucc)/3 else l (C.edge i.castSucc) := by
    simp only [dartSet,Finset.sum_image (fun i _ j _ h => C.edge_injective h),l38BoundaryCost]
  rw [harea,← hcost] at hc
  exact hc

end FaceBoundaryCycle

theorem PennyGraph.boundary_darts_bank_area_bound {n : ℕ} (G : PennyGraph n)
    (P : Fin n→Plane) (u : Plane) (hu : ‖u‖=1)
    (bank : OrientedEdge G→Prop) (l : OrientedEdge G→ℝ) (hl : ∀ e,0≤l e)
    (hdisp : ∀ e : OrientedEdge G,P e.val.2-P e.val.1=l e • carriedVector e)
    (S : Finset (OrientedEdge G)) (hS : ∀ e∈S,G.faceBoundarySuccessor e∈S)
    (hbank : ∀ e∈S,bank e → Real.sqrt 3/2≤ inner ℝ u (sourceNormal e)) :
    4*l38CertificateArea*((∑ e∈S,cross2 (P e.val.1) (P e.val.2))/2)≤
      (∑ e∈S,l38BoundaryCost bank l e)^2 := by
  have hAll : ∀ m : ℕ,∀ T : Finset (OrientedEdge G),T.card=m →
      (∀ e∈T,G.faceBoundarySuccessor e∈T) →
      (∀ e∈T,bank e → Real.sqrt 3/2≤ inner ℝ u (sourceNormal e)) →
      4*l38CertificateArea*((∑ e∈T,cross2 (P e.val.1) (P e.val.2))/2)≤
        (∑ e∈T,l38BoundaryCost bank l e)^2 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro T hcard hT hbankT
      by_cases he : T=∅
      · simp [he]
      · obtain ⟨e,he⟩ := Finset.nonempty_iff_ne_empty.mpr he
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
        have hrec := ih _ hless _ rfl hrest (fun f hf => hbankT f (Finset.mem_sdiff.mp hf).1)
        have hcycle := C.dartSet_bank_area_bound P u hu bank l hl hdisp (fun f hf => hbankT f (hsub hf))
        let a := (∑ f∈C.dartSet,cross2 (P f.val.1) (P f.val.2))/2
        let b := (∑ f∈T\C.dartSet,cross2 (P f.val.1) (P f.val.2))/2
        let L := ∑ f∈C.dartSet,l38BoundaryCost bank l f
        let M := ∑ f∈T\C.dartSet,l38BoundaryCost bank l f
        have hA : (∑ f∈T,cross2 (P f.val.1) (P f.val.2))/2=a+b := by
          have hh := Finset.sum_sdiff (f := fun f => cross2 (P f.val.1) (P f.val.2)) hsub
          dsimp [a,b]
          linarith only [hh]
        have hL : (∑ f∈T,l38BoundaryCost bank l f)=L+M := by
          have hh := Finset.sum_sdiff (f := fun f => l38BoundaryCost bank l f) hsub
          dsimp [L,M]
          linarith only [hh]
        have hLn : 0≤L := Finset.sum_nonneg (fun e _ => l38BoundaryCost_nonneg bank l e (hl e))
        have hMn : 0≤M := Finset.sum_nonneg (fun e _ => l38BoundaryCost_nonneg bank l e (hl e))
        change 4*l38CertificateArea*a≤L^2 at hcycle
        change 4*l38CertificateArea*b≤M^2 at hrec
        rw [hA,hL]
        nlinarith only [hcycle,hrec,mul_nonneg hLn hMn]
  exact hAll S.card S rfl hS hbank

theorem PennyGraph.bounded_signed_area_bank_calibration {n : ℕ} (G : PennyGraph n)
    (P : Fin n→Plane) (u : Plane) (hu : ‖u‖=1)
    (bank : OrientedEdge G→Prop) (l : OrientedEdge G→ℝ) (hl : ∀ e,0≤l e)
    (hdisp : ∀ e : OrientedEdge G,P e.val.2-P e.val.1=l e • carriedVector e)
    (outer : PlaneFace G) (houter : ¬Bornology.IsBounded outer.val)
    (hbank : ∀ e∈G.faceIncidentDarts outer,bank e → Real.sqrt 3/2≤ inner ℝ u (sourceNormal e)) :
    4*l38CertificateArea*(∑ F : BoundedFace G,G.faceSignedArea P (G.boundedFaceAsPlane F))≤
      (∑ e∈G.faceIncidentDarts outer,l38BoundaryCost bank l e)^2 := by
  have hS : ∀ e∈G.faceIncidentDarts outer,G.faceBoundarySuccessor e∈G.faceIncidentDarts outer := by
    intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (G.faceBoundarySuccessor_face e).trans (Finset.mem_filter.mp he).2⟩
  have hh := G.boundary_darts_bank_area_bound P u hu bank l hl hdisp _ hS hbank
  rw [G.bounded_face_signed_area_sum P outer houter]
  simpa only [PennyGraph.faceSignedArea,neg_div,neg_neg] using hh

end Swanepoel
