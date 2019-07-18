
Theorem two_point_per_line:
 forall (Line Point: Type)
        (on: Line -> Point -> Prop)
        (exclude: forall (p: Point) (l: Line), on l p \/ ~ on l p) 
        (point_on_line: forall (l: Line), exists p, (on l p) /\ exists p, (~ on l p))
        (line_for_points: forall (p1 p2: Point),
           p1 = p2 \/
           (exists (l: Line), (on l p1 /\ on l p2) /\
            forall (l1 l2 : Line),
              on l1 p1 /\ on l1 p2 /\ on l2 p1 /\ on l2 p2 -> l1 = l2))
        (par: forall (l: Line) (p: Point) (n: ~on l p),
                exists (lp: Line), ((on lp p)
                                   /\ (forall p1,
                                      (on l p1 -> ~ on lp p1) /\ (on lp p1 -> ~ on l p1)))
                                   /\ forall (lp': Line),
                                        ((on lp' p) /\
                                         forall p1,
                                             (on l p1 -> ~ on lp' p1)
                                          /\ (on lp' p1 -> ~ on l p1) -> lp' = lp))
        (par_or_intersec: forall (l1 l2 : Line),
                  (forall (p: Point), on l1 p -> ~ on l2 p /\
                                      on l1 p -> ~ on l1 p) \/
                  (exists (p: Point), on l1 p /\ on l2 p))
        (line: Line),
  exists (pp: Point*Point),
           ~(fst pp = snd pp) /\
           on line (fst pp) /\ on line (snd pp).
Proof.
 intros.
 destruct (point_on_line line) as [p1in H].
 destruct H as [Hp1line H0].
 destruct H0 as [pout Hpoutline].
 assert (p1in_ne_pout: p1in <> pout).
 { intro. rewrite H in Hp1line. exact (Hpoutline Hp1line). }
 destruct (line_for_points p1in pout).
 { contradict (p1in_ne_pout H). }
 destruct H as [l1 H].
 destruct H as [on_l1 l1_uniq].
 destruct (point_on_line l1) as [ptmp H].
 destruct H as [_ H].
 clear ptmp.
 destruct H as [p2 Hp2out_l1].
 destruct (exclude p2 line).
 - exists (p1in,p2).
   split.
   + intro.
     destruct on_l1. simpl in H0.
     rewrite H0 in H1.
     exact (Hp2out_l1 H1).
   + split.
     * exact Hp1line.
     * exact H.
 - destruct (par l1 p2 Hp2out_l1) as [l2 Hl2].
   destruct Hl2 as [Hl2 l2_uniq].
   destruct (par_or_intersec line l2).
   + destruct (l2_uniq line).
     contradiction (H H1).
   + destruct H0 as [p3 Hp3].
     destruct Hp3 as [Hp3_line Hp2_l2].
     exists (p1in,p3).
     split.
     * destruct Hl2 as [_ Hl2].
       destruct (Hl2 p1in) as [H0 _].
       intro. simpl in H1. subst.
       exact (H0 (proj1 on_l1) Hp2_l2).
     * split.
       ** exact Hp1line.
       ** exact Hp3_line.
Qed.
 
