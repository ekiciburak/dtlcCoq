From DTT Require Import sort.unscoped sort.sort.
Require Import ZArith.

Definition isVal (s: sort): bool :=
  match s with
    | slambda e1 e2 e3 => true
    | spi e1 e2 e3     => true
    | sstar            => true
    | sci n            => true
    | scb b            => true
    | _                => false
  end.

Fixpoint beta (s: sort): sort :=
  match s with
    | sapp (slambda y e1 e2) e3    => subst_sort (e3 .: svar) e2
    | slambda y e1 e2              => slambda y (beta e1) (beta e2)
    | sapp (spi y e1 e2) e3        => subst_sort (e3 .: svar) e2
    | spi y e1 e2                  => spi y (beta e1) (beta e2)
    | ssig y e1 e2                 => ssig y (beta e1) (beta e2)
    | sexst (spair y e1 e2) e3     => subst_sort (e3 .: svar) e2
    | sexst e1 e2                  => sexst (beta e1) e2
    | sapp e1 e2                   => sapp (beta e1) e2
    | splus e1 e2                  => let be1 := beta e1 in
                                      let be2 := beta e2 in
                                      match be1 with
                                        | sci n =>
                                          match be2 with
                                            | sci m => sci (n+m)
                                            | _     => splus be1 be2
                                          end 
                                        | _     => splus be1 be2
                                      end
    | sminus e1 e2                 => let be1 := beta e1 in
                                      let be2 := beta e2 in
                                      match be1 with
                                        | sci n =>
                                          match be2 with
                                            | sci m => sci (n-m)
                                            | _     => sminus be1 be2
                                          end 
                                        | _     => sminus be1 be2
                                      end
    | sgt e1 e2                    => let be1 := beta e1 in
                                      let be2 := beta e2 in
                                      match be1 with
                                        | sci n =>
                                          match be2 with
                                            | sci m => scb (Z.gtb n m)
                                            | _     => sgt be1 be2
                                          end 
                                        | _     => sgt be1 be2
                                      end
    | seq e1 e2                    => let be1 := beta e1 in
                                      let be2 := beta e2 in
                                      match be1 with
                                        | sci n =>
                                          match be2 with
                                            | sci m => scb (Z.eqb n m)
                                            | _     => seq be1 be2
                                          end 
                                        | scb n =>
                                          match be2 with
                                            | scb m => scb (Bool.eqb n m)
                                            | _     => seq be1 be2
                                          end 
                                        | _     => seq be1 be2
                                      end
    | site (scb true) e2 e3        => e2
    | site (scb false) e2 e3       => e3
    | site e1 e2 e3                => site (beta e1) e2 e3 
    | sneg e1                      => let be1 := beta e1 in
                                      match be1 with
                                        | scb b => scb (negb b)
                                        | _     => sneg be1
                                      end
    | sand e1 e2                   => let be1 := beta e1 in
                                      let be2 := beta e2 in
                                      match be1 with
                                        | scb n =>
                                          match be2 with
                                            | scb m => scb (andb n m)
                                            | _     => sand be1 be2
                                          end
                                        | _     => sand be1 be2
                                      end
    | sor e1 e2                    => let be1 := beta e1 in
                                      let be2 := beta e2 in
                                      match be1 with
                                        | scb n =>
                                          match be2 with
                                            | scb m => scb (orb n m)
                                            | _     => sor be1 be2
                                          end
                                        | _     => sor be1 be2
                                      end
    | _                            => s
  end.

Fixpoint betan (n: nat) (s: sort): sort :=
  match n with
    | O   => s
    | S k => if isVal s then s else betan k (beta s) 
  end.
