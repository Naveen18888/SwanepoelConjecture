module
public import Swanepoel.FaceBoundaryOrder
public import Swanepoel.SemicirclePorts
public import Swanepoel.FacePortFive
public import Mathlib.Data.Fintype.Pigeonhole
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

structure FaceBoundaryOrbit {n : ℕ} (G : PennyGraph n) (F : PlaneFace G) where
  length : ℕ
  length_pos : 0<length
  edge : Fin (length+1) → OrientedEdge G
  closes : edge 0=edge (Fin.last length)
  face : ∀ i, G.sourceFace (edge i)=F
  consecutive : ∀ i : Fin length, (edge i.succ).val.2=(edge i.castSucc).val.1
  no_reverse : ∀ i : Fin length, edge i.succ≠reverseEdge (edge i.castSucc)

theorem PennyGraph.exists_face_boundary_orbit {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) (e : OrientedEdge G) (he : G.sourceFace e=F)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a) :
    Nonempty (FaceBoundaryOrbit G F) := by
  let D := {d : OrientedEdge G // G.sourceFace d=F}
  have hnext (d : D) : ∃ p : D,
      p.val.val.2=d.val.val.1 ∧ p.val≠reverseEdge d.val := by
    obtain ⟨b,hvb,hface,hunique⟩ := G.vertex_face_continuation
      d.val.val.1 d.val.val.2 d.val.property
    have hnot : b≠d.val.val.2 := by
      intro hb
      obtain ⟨c,hc,hnc⟩ := hdegree d.val.val.1 d.val.val.2 d.val.property
      exact hnc (hunique hb c hc)
    have hface' : G.sourceFace (reverseEdge ⟨(d.val.val.1,b),hvb⟩)=F :=
      hface.symm.trans d.property
    refine ⟨⟨reverseEdge ⟨(d.val.val.1,b),hvb⟩,hface'⟩,rfl,?_⟩
    intro hrev
    exact hnot (congrArg (fun d : OrientedEdge G => d.val.1) hrev)
  let pred (d : D) : D := Classical.choose (hnext d)
  have hpred (d : D) : (pred d).val.val.2=d.val.val.1 ∧
      (pred d).val≠reverseEdge d.val := Classical.choose_spec (hnext d)
  let seed : D := ⟨e,he⟩
  obtain ⟨i,j,hne,heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => pred^[k] seed)
  have hordered : ∃ i j : ℕ, i<j ∧ pred^[i] seed=pred^[j] seed := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨i,j,h,heq⟩
    · exact ⟨j,i,h,heq.symm⟩
  obtain ⟨i,j,hij,hijEq⟩ := hordered
  let L := j-i
  have hL : 0<L := by dsimp [L]; omega
  let d (k : Fin (L+1)) : D := pred^[i+k.val] seed
  have hsucc (k : Fin L) : d k.succ=pred (d k.castSucc) := by
    dsimp [d]
    rw [show i+(k.val+1)=(i+k.val)+1 by omega,Function.iterate_succ_apply']
  refine ⟨{
    length := L
    length_pos := hL
    edge := fun k => (d k).val
    closes := ?_
    face := fun k => (d k).property
    consecutive := ?_
    no_reverse := ?_ }⟩
  · apply congrArg Subtype.val
    change pred^[i+0] seed=pred^[i+L] seed
    simpa only [Nat.add_zero,show i+L=j by dsimp [L]; omega] using hijEq
  · intro k
    rw [hsucc]
    exact (hpred (d k.castSucc)).1
  · intro k
    rw [hsucc]
    exact (hpred (d k.castSucc)).2

namespace FaceBoundaryOrbit
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} (C : FaceBoundaryOrbit G F)

theorem carried_sum : (∑ i : Fin C.length, carriedVector (C.edge i.castSucc))=0 := by
  let p (k : Fin (C.length+1)) := G.point (C.edge k).val.1
  have hclosed : p (Fin.last C.length)=p 0 := by
    dsimp [p]
    rw [← C.closes]
  have hcarried (i : Fin C.length) : carriedVector (C.edge i.succ)=p i.castSucc-p i.succ := by
    change G.point (C.edge i.succ).val.2-G.point (C.edge i.succ).val.1=_
    rw [C.consecutive i]
  have hsumSucc : (∑ i : Fin C.length, carriedVector (C.edge i.succ))=0 := by
    simp_rw [hcarried]
    calc
      _ = -(∑ i : Fin C.length, (p i.succ-p i.castSucc)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        abel
      _ = 0 := by rw [polygon_edge_sum,hclosed,sub_self,neg_zero]
  have hshift := polygon_edge_sum (fun k => carriedVector (C.edge k))
  rw [Finset.sum_sub_distrib,hsumSucc,← C.closes,sub_self,zero_sub] at hshift
  exact neg_eq_zero.mp hshift

theorem normal_sum : (∑ i : Fin C.length, sourceNormal (C.edge i.castSucc))=0 := by
  simp only [← rightNormalMap_carriedVector]
  rw [← map_sum,C.carried_sum,map_zero]

theorem parallel_consecutive_eq (i : Fin C.length)
    (hc : cross2 (carriedVector (C.edge i.castSucc)) (carriedVector (C.edge i.succ))=0) :
    carriedVector (C.edge i.succ)=carriedVector (C.edge i.castSucc) := by
  rcases unit_cross_zero_eq_or_neg _ _ (carriedVector_norm _) (carriedVector_norm _) hc with h | h
  · exact h
  · have hstart : (C.edge i.succ).val.1=(C.edge i.castSucc).val.2 := by
      apply G.point_injective
      change G.point (C.edge i.succ).val.2-G.point (C.edge i.succ).val.1 =
        -(G.point (C.edge i.castSucc).val.2-G.point (C.edge i.castSucc).val.1) at h
      rw [C.consecutive i,neg_sub] at h
      exact sub_right_inj.mp h
    exact False.elim (C.no_reverse i (Subtype.ext (Prod.ext hstart (C.consecutive i))))

theorem exists_nonparallel_edges : ∃ i j : Fin C.length,
    cross2 (carriedVector (C.edge i.castSucc)) (carriedVector (C.edge j.castSucc)) ≠ 0 := by
  by_contra hn
  have hcross (i j : Fin C.length) :
      cross2 (carriedVector (C.edge i.castSucc)) (carriedVector (C.edge j.castSucc))=0 := by
    by_contra hne
    exact hn ⟨i,j,hne⟩
  have hrepresent (k : Fin (C.length+1)) : ∃ i : Fin C.length, C.edge k=C.edge i.castSucc := by
    by_cases hk : k.val<C.length
    · refine ⟨⟨k.val,hk⟩,?_⟩
      rfl
    · have hlast : k=Fin.last C.length := Fin.ext (by change k.val=C.length; omega)
      refine ⟨⟨0,C.length_pos⟩,?_⟩
      rw [hlast,← C.closes]
      rfl
  have hcrossFull (i j : Fin (C.length+1)) : cross2 (carriedVector (C.edge i))
      (carriedVector (C.edge j))=0 := by
    obtain ⟨a,ha⟩ := hrepresent i
    obtain ⟨b,hb⟩ := hrepresent j
    rw [ha,hb]
    exact hcross a b
  have hconstant (k : Fin (C.length+1)) : carriedVector (C.edge k)=carriedVector (C.edge 0) := by
    refine Fin.induction rfl (fun i ih => ?_) k
    exact (C.parallel_consecutive_eq i (hcrossFull _ _)).trans ih
  have hsum := C.carried_sum
  simp_rw [hconstant] at hsum
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin] at hsum
  have hreal : (C.length : ℝ) • carriedVector (C.edge 0)=0 := by
    simpa only [Nat.cast_smul_eq_nsmul ℝ] using hsum
  have hnonzero : carriedVector (C.edge 0)≠0 := by
    intro hz
    have hu := carriedVector_norm (C.edge 0)
    rw [hz,norm_zero] at hu
    norm_num at hu
  have hzero : (C.length : ℝ)=0 := (smul_eq_zero.mp hreal).resolve_right hnonzero
  have hpos : (0 : ℝ)<C.length := by exact_mod_cast C.length_pos
  linarith

end FaceBoundaryOrbit

theorem PennyGraph.defect_meets_semicircle_of_min_degree {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (hF : F ∈ G.defectPlaneFaces ht)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (v : Plane) (hv : v≠0) :
    ∃ e ∈ G.faceSourcePorts F, 0 < inner ℝ v (sourceNormal e) := by
  have hports := G.defect_source_ports_five_le ht F hF
  obtain ⟨e,he⟩ := Finset.card_pos.mp (show 0<(G.faceSourcePorts F).card by omega)
  have heF := (Finset.mem_filter.mp he).2.2
  obtain ⟨C⟩ := G.exists_face_boundary_orbit F e heF hdegree
  obtain ⟨a,b,hab⟩ := C.exists_nonparallel_edges
  have hnind : cross2 (sourceNormal (C.edge a.castSucc))
      (sourceNormal (C.edge b.castSucc))≠0 := by
    simpa only [← rightNormalMap_carriedVector,rightNormalMap_cross] using hab
  obtain ⟨i,hi⟩ := balanced_normals_meet_every_semicircle
    (fun i : Fin C.length => sourceNormal (C.edge i.castSucc)) C.normal_sum a b hnind v hv
  refine ⟨C.edge i.castSucc,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,C.face _⟩,hi⟩
  apply G.spineSource_of_sourceFace_mem_defects ht
  rw [C.face]
  exact hF

theorem PennyGraph.other_neighbor_of_delete_connected {n : ℕ} (G : PennyGraph n)
    (hn : 3≤n) (hdelete : ∀ a : Fin n, (G.graph.induce {w | w≠a}).Connected)
    (v a : Fin n) (hva : G.graph.Adj v a) :
    ∃ b, G.graph.Adj v b ∧ b≠a := by
  have hthird : ∃ c : Fin n, c≠a ∧ c≠v := by
    by_contra hh
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ {a,v} := by
      intro c _
      by_cases hca : c=a
      · simp only [Finset.mem_insert,Finset.mem_singleton]
        exact Or.inl hca
      · have hcv : c=v := by
          by_contra hcv
          exact hh ⟨c,hca,hcv⟩
        simp only [Finset.mem_insert,Finset.mem_singleton]
        exact Or.inr hcv
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_univ,Fintype.card_fin,Finset.card_pair hva.ne.symm] at hcard
    omega
  obtain ⟨c,hca,hcv⟩ := hthird
  let v' : {w : Fin n | w≠a} := ⟨v,hva.ne⟩
  let c' : {w : Fin n | w≠a} := ⟨c,hca⟩
  have hne : v'≠c' := by
    intro h
    exact hcv (congrArg Subtype.val h).symm
  have hr := (hdelete a).preconnected v' c'
  obtain ⟨b,hb⟩ := hr.nonempty_neighborSet_left hne
  exact ⟨b.val,hb,b.property⟩

theorem PennyGraph.defect_meets_semicircle_of_delete_connected {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (hn : 3≤n)
    (hdelete : ∀ a : Fin n, (G.graph.induce {w | w≠a}).Connected)
    (F : PlaneFace G) (hF : F ∈ G.defectPlaneFaces ht) (v : Plane) (hv : v≠0) :
    ∃ e ∈ G.faceSourcePorts F, 0 < inner ℝ v (sourceNormal e) :=
  G.defect_meets_semicircle_of_min_degree ht F hF
    (G.other_neighbor_of_delete_connected hn hdelete) v hv
end Swanepoel
