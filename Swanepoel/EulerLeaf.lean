module
public import Swanepoel.ContactFaceCount
@[expose] public section

noncomputable section
namespace Swanepoel

private theorem cross_swap (u v : Plane) : cross2 u v = -cross2 v u := by
  unfold cross2
  ring

def tipNeighbourhood (u p : Plane) (r : ℝ) : Set Plane :=
  (leftHalfBall u p r ∪ rightHalfBall (quarterTurn u) p r) ∪ rightHalfBall u p r

theorem isPreconnected_tipNeighbourhood (u p : Plane) (hu : ‖u‖=1)
    {r : ℝ} (hr : 0<r) : IsPreconnected (tipNeighbourhood u p r) := by
  let a := r/4
  have ha : 0<a := by dsimp [a]; positivity
  have hq : ‖quarterTurn u‖=1 := by rw [quarterTurn_norm,hu]
  have hcross : cross2 u (quarterTurn u)=1 := by rw [cross_quarterTurn,hu]; norm_num
  have hrev : cross2 (quarterTurn u) u = -1 := by rw [cross_swap,hcross]
  have hball (s : ℝ) (hs : |s|=a) : p+a • u+s • quarterTurn u∈Metric.ball p r := by
    rw [Metric.mem_ball,dist_eq_norm]
    have he : p+a • u+s • quarterTurn u-p=a • u+s • quarterTurn u := by abel
    rw [he]
    calc
      ‖a • u+s • quarterTurn u‖ ≤ ‖a • u‖+‖s • quarterTurn u‖ := norm_add_le _ _
      _ = a+a := by rw [norm_smul,norm_smul,hu,hq,Real.norm_eq_abs,Real.norm_eq_abs,hs,abs_of_pos ha]; ring
      _ < r := by dsimp [a]; linarith
  have hplus : p+a • u+a • quarterTurn u ∈
      leftHalfBall u p r ∩ rightHalfBall (quarterTurn u) p r := by
    constructor
    · refine ⟨hball a (abs_of_pos ha),?_⟩
      change cross2 u p<cross2 u (p+a • u+a • quarterTurn u)
      simp only [cross2_add_right,cross2_smul_right,cross2_self,hcross,mul_zero,mul_one,add_zero]
      linarith
    · refine ⟨hball a (abs_of_pos ha),?_⟩
      change cross2 (quarterTurn u) (p+a • u+a • quarterTurn u)<cross2 (quarterTurn u) p
      simp only [cross2_add_right,cross2_smul_right,cross2_self,hrev,mul_zero,add_zero]
      linarith
  have hminus : p+a • u+(-a) • quarterTurn u ∈
      rightHalfBall (quarterTurn u) p r ∩ rightHalfBall u p r := by
    constructor
    · refine ⟨hball (-a) (by rw [abs_neg,abs_of_pos ha]),?_⟩
      change cross2 (quarterTurn u) (p+a • u+(-a) • quarterTurn u)<cross2 (quarterTurn u) p
      simp only [cross2_add_right,cross2_smul_right,cross2_self,hrev,mul_zero,add_zero]
      linarith
    · refine ⟨hball (-a) (by rw [abs_neg,abs_of_pos ha]),?_⟩
      change cross2 u (p+a • u+(-a) • quarterTurn u)<cross2 u p
      simp only [cross2_add_right,cross2_smul_right,cross2_self,hcross,mul_zero,mul_one,add_zero]
      linarith
  exact ((isPreconnected_leftHalfBall u p r).union' ⟨_,hplus⟩
    (isPreconnected_rightHalfBall (quarterTurn u) p r)).union' ⟨_,Or.inr hminus.1,hminus.2⟩
    (isPreconnected_rightHalfBall u p r)

theorem PennyGraph.isolated_vertex_free_ball {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (v : Fin n)
    (hv : ∀ f∈S, f.val.1≠v ∧ f.val.2≠v) :
    ∃ r : ℝ, 0<r ∧ r≤1 ∧ ∀ z∈Metric.ball (G.point v) r,
      z∈G.subdrawing S → z=G.point v := by
  let K : Set Plane := (G.point '' {i | i≠v}) ∪ ⋃ f∈S, G.edgeTrace f.val.1 f.val.2
  have hK : IsCompact K := by
    exact ((Set.toFinite {i : Fin n | i≠v}).image G.point).isCompact.union
      (isCompact_iUnion (fun f => isCompact_iUnion (fun _ : f∈S =>
        isCompact_Icc.image (G.continuous_edgePoint f.val.1 f.val.2))))
  have hp : G.point v∉K := by
    rintro (⟨i,hi,hiv⟩ | hf)
    · exact hi (G.point_injective hiv)
    · obtain ⟨f,hf⟩ := Set.mem_iUnion.mp hf
      obtain ⟨hfS,t,⟨ht0,ht1⟩,ht⟩ := Set.mem_iUnion.mp hf
      by_cases h0 : t=0
      · subst t
        have hh : G.point f.val.1=G.point v := by simpa [PennyGraph.edgePoint] using ht
        exact (hv f hfS).1 (G.point_injective hh)
      by_cases h1 : t=1
      · subst t
        have hh : G.point f.val.2=G.point v := by simpa [PennyGraph.edgePoint] using ht
        exact (hv f hfS).2 (G.point_injective hh)
      exact G.edgePoint_ne_vertex _ _ v f.property.2 (lt_of_le_of_ne ht0 (Ne.symm h0))
        (lt_of_le_of_ne ht1 h1) ht
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hK.isClosed.isOpen_compl _ hp
  refine ⟨min r 1,lt_min hr (by norm_num),min_le_right _ _,?_⟩
  intro z hz hdraw
  have hzK := hball ((Metric.ball_subset_ball (min_le_left r 1)) hz)
  rcases hdraw with ⟨i,rfl⟩ | he
  · by_cases hi : i=v
    · rw [hi]
    · exact False.elim (hzK (Or.inl ⟨i,hi,rfl⟩))
  · exact False.elim (hzK (Or.inr he))

theorem PennyGraph.tipNeighbourhood_subset_complement {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) (u p : Plane) (r : ℝ)
    (hfree : ∀ z∈Metric.ball p r, z∈G.subdrawing S → z=p)
    (hline : ∀ z∈G.edgeTrace e.val.1 e.val.2,
      cross2 u z=cross2 u p ∧ cross2 (quarterTurn u) p≤cross2 (quarterTurn u) z) :
    tipNeighbourhood u p r⊆(G.subdrawing (insert e S))ᶜ := by
  intro z hz
  have hball : z∈Metric.ball p r := by
    rcases hz with ((hz | hz) | hz) <;> exact hz.1
  have hne : z≠p := by
    intro heq
    subst z
    rcases hz with ((hz | hz) | hz) <;>
      exact (lt_irrefl _) (by simpa only [Set.mem_ofPred_eq] using hz.2)
  rw [G.subdrawing_insert]
  rintro (hold | hnew)
  · exact hne (hfree z hball hold)
  · have hl := hline z hnew
    rcases hz with ((hz | hz) | hz)
    · exact (not_lt_of_ge hl.1.le) hz.2
    · exact (not_lt_of_ge hl.2) hz.2
    · exact (not_lt_of_ge hl.1.ge) hz.2

private theorem backward_offsets_mem_tip (u p : Plane) (hu : ‖u‖=1)
    {a d r : ℝ} (ha : 0≤a) (hd : 0<d) (hr : a+d<r) :
    p+(-a) • u+d • quarterTurn u∈tipNeighbourhood u p r ∧
      p+(-a) • u+(-d) • quarterTurn u∈tipNeighbourhood u p r := by
  have hq : ‖quarterTurn u‖=1 := by rw [quarterTurn_norm,hu]
  have hc : cross2 u (quarterTurn u)=1 := by rw [cross_quarterTurn,hu]; norm_num
  have hball (s : ℝ) (hs : |s|=d) : p+(-a) • u+s • quarterTurn u∈Metric.ball p r := by
    rw [Metric.mem_ball,dist_eq_norm]
    have he : p+(-a) • u+s • quarterTurn u-p=(-a) • u+s • quarterTurn u := by abel
    rw [he]
    calc
      ‖(-a) • u+s • quarterTurn u‖≤‖(-a) • u‖+‖s • quarterTurn u‖ := norm_add_le _ _
      _ = a+d := by
        rw [norm_smul,norm_smul,hu,hq,Real.norm_eq_abs,Real.norm_eq_abs,hs,abs_neg,abs_of_nonneg ha]
        ring
      _ < r := hr
  constructor
  · refine Or.inl (Or.inl ⟨hball d (abs_of_pos hd),?_⟩)
    change cross2 u p<cross2 u (p+(-a) • u+d • quarterTurn u)
    simp only [cross2_add_right,cross2_smul_right,cross2_self,hc,mul_zero,mul_one,add_zero]
    linarith
  · refine Or.inr ⟨hball (-d) (by rw [abs_neg,abs_of_pos hd]),?_⟩
    change cross2 u (p+(-a) • u+(-d) • quarterTurn u)<cross2 u p
    simp only [cross2_add_right,cross2_smul_right,cross2_self,hc,mul_zero,mul_one,add_zero]
    linarith

theorem PennyGraph.insert_edge_sides_eq_of_isolated_right {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) (he : e∉S)
    (hv : ∀ f∈S, f.val.1≠e.val.2 ∧ f.val.2≠e.val.2) :
    connectedComponentIn (G.subdrawing (insert e S))ᶜ (G.edgeSidePoint S e true (1/2))=
      connectedComponentIn (G.subdrawing (insert e S))ᶜ (G.edgeSidePoint S e false (1/2)) := by
  obtain ⟨r,hr,hr1,hfree⟩ := G.isolated_vertex_free_ball S e.val.2 hv
  let u := G.point e.val.2-G.point e.val.1
  let p := G.point e.val.2
  let a := r/4
  let t := 1-a
  have ha : 0<a := by dsimp [a]; positivity
  have ht0 : 0<t := by dsimp [t,a]; linarith
  have ht1 : t<1 := by dsimp [t]; linarith
  have hu : ‖u‖=1 := by simpa only [u,← dist_eq_norm] using e.property.2.symm.2
  have hline : ∀ z∈G.edgeTrace e.val.1 e.val.2,
      cross2 u z=cross2 u p ∧ cross2 (quarterTurn u) p≤cross2 (quarterTurn u) z := by
    rintro z ⟨s,⟨hs0,hs1⟩,rfl⟩
    have hp : G.edgePoint e.val.1 e.val.2 s=p+(s-1) • u := by
      dsimp [PennyGraph.edgePoint,p,u]
      module
    have hc : cross2 (quarterTurn u) u = -1 := by
      rw [cross_swap,cross_quarterTurn,hu]; norm_num
    rw [hp]
    simp only [cross2_add_right,cross2_smul_right,cross2_self,hc,mul_zero,add_zero]
    exact ⟨by trivial,by linarith⟩
  have hsub := G.tipNeighbourhood_subset_complement S e u p r hfree hline
  have hspec := G.edgeClearance_spec S e he ht0 ht1
  have hd : a+G.edgeClearance S e t<r := by
    have hb : 2*G.edgeClearance S e t<a := by simpa only [t,sub_sub_cancel] using hspec.2.2.1
    dsimp [a] at *
    linarith
  have hmem := backward_offsets_mem_tip u p hu ha.le hspec.1 hd
  have heq (left : Bool) : G.edgeSidePoint S e left t=
      p+(-a) • u+(if left then G.edgeClearance S e t else -G.edgeClearance S e t) • quarterTurn u := by
    unfold PennyGraph.edgeSidePoint
    congr 1
    dsimp [PennyGraph.edgePoint,p,u,t]
    module
  have heqtrue : G.edgeSidePoint S e true t=
      p+(-a) • u+G.edgeClearance S e t • quarterTurn u := by simpa using heq true
  have heqfalse : G.edgeSidePoint S e false t=
      p+(-a) • u+(-G.edgeClearance S e t) • quarterTurn u := by simpa using heq false
  rw [← heqtrue,← heqfalse] at hmem
  have hsame := (isPreconnected_tipNeighbourhood u p hu hr).subset_connectedComponentIn
    hmem.1 hsub hmem.2
  exact (connectedComponentIn_eq (G.edgeSidePoint_in_fixed_component S e he true ht0 ht1)).trans
    ((connectedComponentIn_eq hsame).trans
      (connectedComponentIn_eq (G.edgeSidePoint_in_fixed_component S e he false ht0 ht1)).symm)

private theorem quarterTurn_neg (u : Plane) : quarterTurn (-u) = -quarterTurn u := by
  ext i
  fin_cases i <;> simp [quarterTurn]

theorem PennyGraph.insert_edge_sides_eq_of_isolated_left {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) (he : e∉S)
    (hv : ∀ f∈S, f.val.1≠e.val.1 ∧ f.val.2≠e.val.1) :
    connectedComponentIn (G.subdrawing (insert e S))ᶜ (G.edgeSidePoint S e true (1/2))=
      connectedComponentIn (G.subdrawing (insert e S))ᶜ (G.edgeSidePoint S e false (1/2)) := by
  obtain ⟨r,hr,hr1,hfree⟩ := G.isolated_vertex_free_ball S e.val.1 hv
  let u := G.point e.val.1-G.point e.val.2
  let p := G.point e.val.1
  let a := r/4
  let t := a
  have ha : 0<a := by dsimp [a]; positivity
  have ht0 : 0<t := ha
  have ht1 : t<1 := by dsimp [t,a]; linarith
  have hu : ‖u‖=1 := by simpa only [u,← dist_eq_norm] using e.property.2.2
  have hline : ∀ z∈G.edgeTrace e.val.1 e.val.2,
      cross2 u z=cross2 u p ∧ cross2 (quarterTurn u) p≤cross2 (quarterTurn u) z := by
    rintro z ⟨s,⟨hs0,hs1⟩,rfl⟩
    have hp : G.edgePoint e.val.1 e.val.2 s=p+(-s) • u := by
      dsimp [PennyGraph.edgePoint,p,u]
      module
    have hc : cross2 (quarterTurn u) u = -1 := by
      rw [cross_swap,cross_quarterTurn,hu]; norm_num
    rw [hp]
    simp only [cross2_add_right,cross2_smul_right,cross2_self,hc,mul_zero,add_zero]
    exact ⟨by trivial,by linarith⟩
  have hsub := G.tipNeighbourhood_subset_complement S e u p r hfree hline
  have hspec := G.edgeClearance_spec S e he ht0 ht1
  have hd : a+G.edgeClearance S e t<r := by
    have hb : 2*G.edgeClearance S e t<a := hspec.2.1
    dsimp [a] at *
    linarith
  have hmem := backward_offsets_mem_tip u p hu ha.le hspec.1 hd
  have hdir : quarterTurn (G.point e.val.2-G.point e.val.1) = -quarterTurn u := by
    have hh : G.point e.val.2-G.point e.val.1 = -u := by dsimp [u]; abel
    rw [hh,quarterTurn_neg]
  have heqtrue : G.edgeSidePoint S e true t=
      p+(-a) • u+(-G.edgeClearance S e t) • quarterTurn u := by
    dsimp [PennyGraph.edgeSidePoint]
    rw [hdir]
    dsimp [PennyGraph.edgePoint,p,u,t]
    module
  have heqfalse : G.edgeSidePoint S e false t=
      p+(-a) • u+G.edgeClearance S e t • quarterTurn u := by
    dsimp [PennyGraph.edgeSidePoint]
    rw [hdir]
    dsimp [PennyGraph.edgePoint,p,u,t]
    module
  rw [← heqfalse,← heqtrue] at hmem
  have hsame := (isPreconnected_tipNeighbourhood u p hu hr).subset_connectedComponentIn
    hmem.2 hsub hmem.1
  exact (connectedComponentIn_eq (G.edgeSidePoint_in_fixed_component S e he true ht0 ht1)).trans
    ((connectedComponentIn_eq hsame).trans
      (connectedComponentIn_eq (G.edgeSidePoint_in_fixed_component S e he false ht0 ht1)).symm)

theorem PennyGraph.subdrawing_face_count_insert_of_isolated_right {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) (he : e∉S)
    (hv : ∀ f∈S, f.val.1≠e.val.2 ∧ f.val.2≠e.val.2) :
    (G.subdrawingFaces (insert e S)).ncard=(G.subdrawingFaces S).ncard := by
  rw [G.subdrawing_face_count_insert S e he,
    ite_eq_left (G.insert_edge_sides_eq_of_isolated_right S e he hv),add_zero]

theorem PennyGraph.subdrawing_face_count_insert_of_isolated_left {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) (he : e∉S)
    (hv : ∀ f∈S, f.val.1≠e.val.1 ∧ f.val.2≠e.val.1) :
    (G.subdrawingFaces (insert e S)).ncard=(G.subdrawingFaces S).ncard := by
  rw [G.subdrawing_face_count_insert S e he,
    ite_eq_left (G.insert_edge_sides_eq_of_isolated_left S e he hv),add_zero]

end Swanepoel
