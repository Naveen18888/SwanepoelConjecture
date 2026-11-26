module
public import Swanepoel.FaceBoundaryPermutationCycles
public import Swanepoel.MonotoneCapChainSides
public import Swanepoel.UnitCapPenny
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

namespace FaceBoundaryCycle
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} {initial : OrientedEdge G}
    (C : FaceBoundaryCycle G F initial)

def vertexAt (i : ℕ) : Fin n :=
  C.vertex ⟨min i C.length,Nat.lt_succ_of_le (min_le_right _ _)⟩

theorem vertexAt_eq (i : ℕ) (hi : i ≤ C.length) :
    C.vertexAt i=C.vertex ⟨i,Nat.lt_succ_of_le hi⟩ := by
  apply congrArg C.vertex
  exact Fin.ext (min_eq_left hi)

theorem vertexAt_closes : C.vertexAt C.length=C.vertexAt 0 := by
  rw [C.vertexAt_eq _ le_rfl,C.vertexAt_eq _ (Nat.zero_le _)]
  exact C.vertex_closes

theorem vertexAt_edge (i : ℕ) (hi : i < C.length) :
    (C.edge (⟨i,hi⟩ : Fin C.length).castSucc).val=
      (C.vertexAt i,C.vertexAt (i+1)) := by
  apply Prod.ext
  · rw [C.vertexAt_eq i hi.le]
    rfl
  · rw [C.vertexAt_eq (i+1) (by omega)]
    exact C.edge_end ⟨i,hi⟩

theorem vertexAt_contact (i : ℕ) (hi : i < C.length) :
    G.graph.Adj (C.vertexAt i) (C.vertexAt (i+1)) := by
  have h := (C.edge (⟨i,hi⟩ : Fin C.length).castSucc).property
  rwa [C.vertexAt_edge i hi] at h

theorem vertexAt_no_backtrack
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (i : ℕ) (hi : i+2 ≤ C.length) : C.vertexAt i ≠ C.vertexAt (i+2) := by
  intro heq
  let j : Fin C.length := ⟨i,by omega⟩
  let k : Fin C.length := ⟨i+1,by omega⟩
  apply C.no_reverse hdegree j
  have hindex : j.succ=k.castSucc := Fin.ext rfl
  rw [hindex]
  apply Subtype.ext
  rw [C.vertexAt_edge _ k.isLt]
  change (C.vertexAt (i+1),C.vertexAt (i+2))=
    ((C.edge j.castSucc).val.2,(C.edge j.castSucc).val.1)
  rw [C.vertexAt_edge _ j.isLt]
  exact Prod.ext rfl heq.symm

theorem three_le_length
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a) :
    3 ≤ C.length := by
  by_contra hn
  have hc : C.length=1 ∨ C.length=2 := by have := C.length_pos; omega
  rcases hc with h1 | h2
  · have heq : C.vertexAt 1=C.vertexAt 0 := by simpa only [h1] using C.vertexAt_closes
    exact (C.vertexAt_contact 0 C.length_pos).ne heq.symm
  · have heq : C.vertexAt 2=C.vertexAt 0 := by simpa only [h2] using C.vertexAt_closes
    exact C.vertexAt_no_backtrack hdegree 0 (by omega) heq.symm

theorem tail_projection_monotone (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht)
    (axis : Plane →ₗ[ℝ] ℝ)
    (hunique : ∀ e∈G.faceSourcePorts F, axis (carriedVector e)<0 → e=initial) :
    Monotone (fun i : ℕ => axis (G.point (C.vertexAt (i+1)))) := by
  apply monotone_nat_of_le_succ
  intro i
  by_cases hi : i+1 < C.length
  · let j : Fin C.length := ⟨i+1,hi⟩
    have hnonneg : 0 ≤ axis (carriedVector (C.edge j.castSucc)) := by
      by_contra hn
      have heq := hunique _ (C.port_membership ht hF j) (lt_of_not_ge hn)
      have hz := C.initial_occurs_once j heq
      change i+1=0 at hz
      omega
    have he := C.vertexAt_edge (i+1) hi
    change 0 ≤ axis (G.point (C.edge j.castSucc).val.2-
      G.point (C.edge j.castSucc).val.1) at hnonneg
    rw [he,map_sub] at hnonneg
    linarith
  · have hclamp : C.vertexAt (i+1)=C.vertexAt (i+1+1) := by
      dsimp [vertexAt]
      apply congrArg C.vertex
      apply Fin.ext
      simp only [min_eq_right (by omega : C.length ≤ i+1),
        min_eq_right (by omega : C.length ≤ i+1+1)]
    rw [hclamp]

end FaceBoundaryCycle

theorem PennyGraph.unique_negative_port_forces_cap_rhombus {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (hF : F∈G.defectPlaneFaces ht)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (initial : OrientedEdge G) (hface : G.sourceFace initial=F)
    (axis : Plane →ₗ[ℝ] ℝ) (hnegative : axis (carriedVector initial)<0)
    (hunique : ∀ e∈G.faceSourcePorts F, axis (carriedVector e)<0 → e=initial) :
    ∃ (C : RhombusCell G) (last : OrientedEdge G),
      initial.val=(C.b,C.a) ∧ last.val=(C.c,C.b) ∧ G.sourceFace last=F ∧ axis C.v=0 := by
  obtain ⟨Q⟩ := G.minimal_face_boundary_cycle F initial hface
  have hL := Q.three_le_length hdegree
  let k := Q.length-1
  let p (i : ℕ) := Q.vertexAt (i+1)
  have hk : 2≤k := by dsimp [k]; omega
  have hfirst : initial.val=(Q.vertexAt 0,Q.vertexAt 1) := by
    exact (congrArg Subtype.val Q.starts).symm.trans (Q.vertexAt_edge 0 Q.length_pos)
  have hp0 : p 0=initial.val.2 := (congrArg Prod.snd hfirst).symm
  have hpk : p k=initial.val.1 := by
    dsimp [p,k]
    rw [show Q.length-1+1=Q.length by omega,Q.vertexAt_closes]
    exact (congrArg Prod.fst hfirst).symm
  have hcontact (i : ℕ) (hi : i<k) : G.graph.Adj (p i) (p (i+1)) := by
    exact Q.vertexAt_contact (i+1) (by dsimp [k] at hi; omega)
  have hback (i : ℕ) (hi : i+2≤k) : p i≠p (i+2) := by
    exact Q.vertexAt_no_backtrack hdegree (i+1) (by dsimp [k] at hi; omega)
  have hmono : Monotone (fun i : ℕ => axis (G.point (p i))) :=
    Q.tail_projection_monotone ht hF axis hunique
  have hcap : G.graph.Adj (p 0) (p k) := by rw [hp0,hpk]; exact initial.property.symm
  have hpositive : 0 < axis (G.point (p k)-G.point (p 0)) := by
    rw [hp0,hpk]
    have hn : G.point initial.val.1-G.point initial.val.2= -carriedVector initial := by
      dsimp [carriedVector]
      abel
    rw [hn,map_neg]
    linarith
  obtain ⟨hind,hside⟩ := G.monotone_cap_chain_cross_ratio axis p hk hcap hpositive
    hcontact hback hmono
  have hac : G.graph.Adj initial.val.2 (p 1) := by
    simpa only [hp0] using hcontact 0 (by omega)
  have hbd : G.graph.Adj initial.val.1 (p (k-1)) := by
    have h := (hcontact (k-1) (by omega)).symm
    simpa only [show k-1+1=k by omega,hpk] using h
  have hacAxis : 0 ≤ axis (G.point (p 1)-G.point initial.val.2) := by
    have hh := hmono (show 0≤(1:ℕ) by omega)
    change axis (G.point (p 0))≤axis (G.point (p 1)) at hh
    rw [hp0] at hh
    rw [map_sub]
    linarith
  have hbdAxis : axis (G.point (p (k-1))-G.point initial.val.1) ≤ 0 := by
    have hh := hmono (show k-1≤k by omega)
    change axis (G.point (p (k-1)))≤axis (G.point (p k)) at hh
    rw [hpk] at hh
    rw [map_sub]
    linarith
  rw [hp0,hpk] at hpositive hind hside
  obtain ⟨C,ha,hb,hc,hd,_,hz⟩ := G.unit_cap_forces_rhombus ht
    initial.val.2 initial.val.1 (p 1) (p (k-1)) initial.property.symm hac hbd
    axis hpositive hacAxis hbdAxis hind hside
  let j : Fin Q.length := ⟨Q.length-1,by omega⟩
  let last := Q.edge j.castSucc
  have hlast : last.val=(p (k-1),initial.val.1) := by
    have hdlast : p (k-1)=Q.vertexAt (Q.length-1) := by
      dsimp [p,k]
      congr 1
      omega
    have hend : Q.vertexAt (Q.length-1+1)=initial.val.1 := by
      rw [show Q.length-1+1=Q.length by omega,Q.vertexAt_closes]
      exact (congrArg Prod.fst hfirst).symm
    calc
      last.val = (Q.vertexAt (Q.length-1),Q.vertexAt (Q.length-1+1)) :=
        Q.vertexAt_edge (Q.length-1) (by omega)
      _ = _ := by rw [← hdlast,hend]
  refine ⟨C,last,?_,?_,Q.face _,?_⟩
  · rw [ha,hb]
  · rw [hc,hb]
    exact hlast
  · simpa only [RhombusCell.v,ha,hd] using hz

end Swanepoel
