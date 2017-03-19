// follower(_) ->
//   receive
//     {new_ldr, C} ->
//       C ! {new_flwr, self()},
//       follower(C)
//  end.
//
// leader(Flwrs) ->
//   receive
//     {new_flwr, C} ->
//       leader(Flwrs + C);
//     {new_ldr, C} ->
//       C ! {new_flwr, self()},
//       Flwrs ! {new_ldr, C},
//       follower(C)
//   end.
//
// environment nondeterministically
// (1) creates new leader actors with empty Buffer/Flwrs
// (2) destroys leader actors with empty Buffer/Flwrs messages
// (3) sends new_ldr messages
//
////////////////////////////////////////

type message_type;

constant new_ldr : message_type;
constant new_flwr : message_type;

type state_type;

constant leader : state_type;
constant follower : state_type;

// Fields of messages
var MessageType : [ref]message_type;
var Sender : [ref]ref;

// Fields of actors
var State : [ref]state_type;
var Leader : [ref]ref;
var Flwrs : [ref,ref]bool;
var Buffer : [ref,ref]bool;

procedure World() {
  var Actors : [ref]bool;
  var Messages : [ref]bool;
  var activeActor : ref;
  var receiverActor : ref;
  var message : ref;
  var message2 : ref;
  var TmpBuffer : [ref,ref]bool;
  var TmpFlwrs : [ref,ref]bool;

  init: 
    assume (forall x : ref :: !Actors[x]);
    assume (forall x : ref :: !Messages[x]);
    goto loop_head;
  
  loop_head:
    assert (forall x : ref, y : ref :: Actors[x] && State[x] == leader && Follower[x,y] ==> 
                       State[y] == follower);
    // inductive invariant that implies assert statement:
    // (forall x : ref, y : ref :: Actors[x] && State[x] == leader && Follower[x,y] ==> 
    // 	       	   State[y] == follower) &&
    // (forall x : ref :: Messages[x] && MessageType[x] == new_flwr ==> 
    // 	       	   State[Sender[x]] = follower && Actors[Sender[x]]) &&
    // (forall x : ref, y : ref :: Actors[x] && Buffer[x,y] ==> Messages[y])
    goto choose_env_action, choose_actor;
    
  choose_env_action:
    goto create_actor, kill_actor, send_new_ldr;

  create_actor:
    havoc activeActor;
    assume !Actors[activeActor];
    assume (forall x : ref :: !Buffer[activeActor,x]);
    assume (forall x : ref :: !Flwrs[activeActor,x]);
    Actors[activeActor] := true;
    goto loop_head;

  kill_actor:
    havoc activeActor;
    assume Actors[activeActor];
    assume State[activeActor] = leader;
    assume (forall x : ref :: !Buffer[activeActor,x]);
    assume (forall x : ref :: !Flwrs[activeActor,x]);
    assume (forall x : ref, y : ref :: Actors[x] && Buffer[x,y] ==> Sender[y] != activeCar); 
    Actors[activeActor] := false;

  send_new_ldr:
    havoc activeActor, receiverActor, message;
    assume Actors[activeActor] && State[activeActor] == leader;
    assume Actors[receiverActor] && State[receiverActor] == leader;
    assume activeActor != receiverActor;
    assume (forall x : ref :: !Buffer[activeCar,x] && !Buffer[receiverCar,x]);
    assume !Messages[message];
    Sender[message] := activeActor;
    MessageType[message] := new_ldr;
    Buffer[receiverCar,message] := true;

  choose_actor:
    havoc activeActor, message;
    assume Actors[activeActor];
    assume Buffer[activeActor,message];
    Buffer[activeActor,message] := false;
    goto active_is_leader, active_is_follower;

  active_is_leader:
    assume State[activeActor] == leader;
    goto leader_process_new_flwr, leader_process_new_ldr;

  leader_process_new_flwr:
    assume MessageType[message] == new_flwr;
    Flwrs[activeActor,Sender[message]] := true;
    goto loop_head;

  leader_process_new_ldr: 
    assume MessageType[message] == new_ldr;

    // accept new leader
    Leader[activeActor] := Sender[message];
    State[activeActor] := follower;

    // broadcast message to all followers
    TmpBuffer := Buffer;
    havoc Buffer;
    assume (forall x : ref, y : ref :: !Flwrs[activeActor,x] ==> Buffer[x,y] == TmpBuffer[x,y]);
    assume (forall x : ref, y : ref :: Flwrs[activeActor,x] ==> Buffer[x,y] == TmpBuffer[x,y] || 
                                       y == message && Buffer[x,message]);
    
    // remove links to all followers
    TmpFlwrs := Flwrs;
    havoc Flwrs;
    assume (forall x : ref, y : ref :: x != activeActor ==> Flwrs[x,y] == TmpFlwrs[x,y]);
    assume (forall x : ref :: !Flwrs[activeActor,x]);
 
    // send new_flwr message to new leader;
    havoc message2;
    assume !Messages[message2];
    MessageType[message2] := new_flwr;
    Sender[message2] := activeActor;
    Buffer[Sender[message],message2] := true;
    goto loop_head;

  active_is_follower:
    assume State[activeActor] == follower;
    goto follower_process_new_ldr, follower_process_new_flwr;

  follower_process_new_ldr:
    assume MessageType[message] == new_ldr;
    Leader[activeActor] := Sender[message];
    goto loop_head;

  follower_process_new_flwr:
    assume MessageType[message] == new_flwr;
    goto loop_head;
}
