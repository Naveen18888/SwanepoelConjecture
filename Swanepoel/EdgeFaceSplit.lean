module
public import Swanepoel.EdgeSides
@[expose] public section

noncomputable section
namespace Swanepoel

private theorem component_closure_within_ambient (U : Set Plane) {p z : Plane}
    (hp : p∈U) (hz : z∈closure (connectedComponentIn U p)) (hzU : z∈U) :
    z∈connectedComponentIn U p := by
  rw [connectedComponentIn_eq_image hp] at hz ⊢
  have hc := (Topology.IsInducing.subtypeVal (t := U)).closure_eq_preimage_closure_image
    (connectedComponent (⟨p,hp⟩ : U))
  have hz' : (⟨z,hzU⟩ : U)∈closure (connectedComponent (⟨p,hp⟩ : U)) := by
    rw [hc]
    exact hz
  exact ⟨⟨z,hzU⟩,isClosed_connectedComponent.closure_subset hz',rfl⟩

theorem PennyGraph.insert_edge_at_most_two_components {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) (he : e∉S)
    {x : Plane}
    (hxU : x∈connectedComponentIn (G.subdrawing S)ᶜ (G.edgePoint e.val.1 e.val.2 (1/2)))
    (hxW : x∈(G.subdrawing (insert e S))ᶜ) :
    connectedComponentIn (G.subdrawing (insert e S))ᶜ x=
        connectedComponentIn (G.subdrawing (insert e S))ᶜ (G.edgeSidePoint S e true (1/2)) ∨
    connectedComponentIn (G.subdrawing (insert e S))ᶜ x=
        connectedComponentIn (G.subdrawing (insert e S))ᶜ (G.edgeSidePoint S e false (1/2)) := by
  classical
  let p := G.edgePoint e.val.1 e.val.2 (1/2)
  let U := connectedComponentIn (G.subdrawing S)ᶜ p
  let W := (G.subdrawing (insert e S))ᶜ
  let V := connectedComponentIn W x
  have hWO : W⊆(G.subdrawing S)ᶜ := by
    intro z hz hdraw
    exact hz (by rw [G.subdrawing_insert]; exact Or.inl hdraw)
  have hVW : V⊆W := connectedComponentIn_subset _ _
  have hVU : V⊆U := by
    have hsub := isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hxW) (hVW.trans hWO)
    rw [← connectedComponentIn_eq hxU] at hsub
    exact hsub
  have hxV : x∈V := mem_connectedComponentIn hxW
  have hpOld : p∈(G.subdrawing S)ᶜ :=
    Set.disjoint_left.mp (G.omitted_edge_disjoint_subdrawing S e he)
      ⟨1/2,⟨by norm_num,by norm_num⟩,rfl⟩
  have hpU : p∈U := mem_connectedComponentIn hpOld
  have hpNotW : p∉W := by
    intro hp
    apply hp
    rw [G.subdrawing_insert]
    exact Or.inr ⟨1/2,⟨by norm_num,by norm_num⟩,rfl⟩
  have hVopen : IsOpen V := (G.isCompact_subdrawing (insert e S)).isClosed.isOpen_compl.connectedComponentIn
  have hex : ∃ z, z∈closure V ∧ z∈U ∧ z∉V := by
    by_contra hn
    push Not at hn
    have hUsub : U⊆V := isPreconnected_connectedComponentIn.subset_of_closure_inter_subset
      hVopen ⟨x,hxU,hxV⟩ (fun z hz => hn z hz.1 hz.2)
    exact hpNotW (hVW (hUsub hpU))
  obtain ⟨z,hzcl,hzU,hzNotV⟩ := hex
  have hzOld : z∈(G.subdrawing S)ᶜ := connectedComponentIn_subset _ _ hzU
  have hzNotW : z∉W := fun hzW => hzNotV (component_closure_within_ambient W hxW hzcl hzW)
  have hzDraw : z∈G.subdrawing (insert e S) := not_not.mp hzNotW
  rw [G.subdrawing_insert] at hzDraw
  have hzEdge : z∈G.edgeTrace e.val.1 e.val.2 := hzDraw.resolve_left hzOld
  obtain ⟨t,⟨ht0,ht1⟩,hparam⟩ := hzEdge
  have htne0 : t≠0 := by
    intro ht
    have hzEq : z=G.point e.val.1 := by
      rw [ht] at hparam
      simpa [PennyGraph.edgePoint] using hparam.symm
    exact hzOld (hzEq.symm ▸ Or.inl ⟨e.val.1,rfl⟩)
  have htne1 : t≠1 := by
    intro ht
    have hzEq : z=G.point e.val.2 := by
      rw [ht] at hparam
      simpa [PennyGraph.edgePoint] using hparam.symm
    exact hzOld (hzEq.symm ▸ Or.inl ⟨e.val.2,rfl⟩)
  have ht0' : 0<t := lt_of_le_of_ne ht0 htne0.symm
  have ht1' : t<1 := lt_of_le_of_ne ht1 htne1
  have hd := (G.edgeClearance_spec S e he ht0' ht1').1
  have hlocal := G.edgeClearance_ball_complement S e he ht0' ht1'
  have hcl : G.edgePoint e.val.1 e.val.2 t∈closure V := hparam.symm ▸ hzcl
  obtain ⟨y,hyBall,hyV⟩ := mem_closure_iff.mp hcl
    (Metric.ball (G.edgePoint e.val.1 e.val.2 t) (2*G.edgeClearance S e t))
    Metric.isOpen_ball (Metric.mem_ball_self (by linarith))
  have hySides : y∈
      leftHalfBall (G.point e.val.2-G.point e.val.1) (G.edgePoint e.val.1 e.val.2 t)
        (2*G.edgeClearance S e t) ∪
      rightHalfBall (G.point e.val.2-G.point e.val.1) (G.edgePoint e.val.1 e.val.2 t)
        (2*G.edgeClearance S e t) := by
    rw [← hlocal]
    exact ⟨hyBall,hVW hyV⟩
  have hVeq : V=connectedComponentIn W y := connectedComponentIn_eq hyV
  have hfixed := G.edge_sides_in_fixed_components S e he ht0' ht1'
  rcases hySides with hyL | hyR
  · exact Or.inl (hVeq.trans (connectedComponentIn_eq (hfixed.1 hyL)).symm)
  · exact Or.inr (hVeq.trans (connectedComponentIn_eq (hfixed.2 hyR)).symm)

end Swanepoel
