Require Import Coq.Strings.String.
Require Import PrefixSerializableDefinitions PrefixSerializable TrustedTickBox.

Local Open Scope string_scope.
Set Implicit Arguments.

Definition TickBoxState_Serializable {T} `{Serializable T} : Serializable (TickBoxPreState T)
  := {| to_string st := match st with
                          | NoData ticks => "NoData " ++ to_string ticks
                          | InitiallyWaitingOnData ticks => "InitiallyWaitingOnData " ++ to_string ticks
                          | HaveData ticks data publishesSinceLastChange
                            => "HaveData " ++ to_string ticks ++ " " ++ to_string data ++ " " ++ to_string publishesSinceLastChange
                          | WaitingOnData ticks publishesSinceLastChange
                            => "WaitingOnData " ++ to_string ticks ++ " " ++ to_string publishesSinceLastChange
                          | WaitingOnTicks ticks publishesSinceLastChange
                            => "WaitingOnTicks " ++ to_string ticks ++ " " ++ to_string publishesSinceLastChange
                        end |}.

Hint Extern 1 (Serializable (TickBoxPreState _)) => apply TickBoxState_Serializable : typeclass_instances.

Instance PublishDurationT_Serializable : Serializable PublishDurationT
  := {| to_string n := match n with
                          | durationOf n => to_string n
                          | inf => "∞"
                       end |}.

Instance tbConfigInput_Serializable : Serializable tbConfigInput
  := {| to_string ev := match ev with
                          | tbSetPublishInterval n => "tbSetPublishInterval " ++ to_string n
                          | tbSetPublishDuration n => "tbSetPublishDuration " ++ to_string n
                          | tbSetWaitBeforeUpdateInterval n => "tbSetWaitBeforeUpdateInterval " ++ to_string n
                          | tbSetPublishPrecision n => "tbSetPublishPrecision " ++ to_string n
                        end |}.

Definition tbEventInput_Serializable {T} `{Serializable T} : Serializable (tbEventInput T)
  := {| to_string ev := match ev with
                          | tbNotifyChange => "tbNotifyChange"
                          | tbTick addedTickCount => "tbTick " ++ to_string addedTickCount
                          | tbValueReady val => "tbValueReady " ++ to_string val
                        end |}.

Hint Extern 1 (Serializable (tbEventInput _)) => apply tbEventInput_Serializable : typeclass_instances.

Hint Extern 0 (Serializable (tbInput _)) => unfold tbInput : typeclass_instances.
