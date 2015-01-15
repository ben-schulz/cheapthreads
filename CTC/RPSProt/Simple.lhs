--
-- this is ~/cheapthreads/CTC/RPSProt/Simple.hs
--
-- a first example of RPS to specify a protocol
--
-- put here 2011.02.11
--
-- Schulz
--

> module Simple where

> import MonadicConstructions
> import Combinators

For starters, let's implement a very, very simple protocol,
consisting of a client and a server, with only requests, replies, and faults.

The session starts when the client sends a request; the server may reply,
or may fault, in which case the client may retry:

> type Stamp = Int
> data Req' = Query Stamp | Retry Stamp 
> data Rsp' = Reply Stamp | Fault

> type Req = Event Req'
> type Rsp = Event Rsp' 

> stampof (Msg (Query n)) = n
> stampof (Msg (Retry n)) = n

It is also necessary to model the essential asynchronicity of communication
between hosts; computation may occur in the absence of any incoming or
outgoing messages.  There are two instances in which this may occur:
either when the host is performing internal computations that are necessary
in order to continue with the computation, or when the host is simply waiting
for an incoming message.  This is modeled using a modified 'Maybe' construct,
namely 'Event'.

The 'Msg' constructor simply wraps a message of the parameter type; 'Working'
indicates that the host is performing internal computations; 'Listen'
corresponds to a state in which the host is awaiting a message but performing
no other activity.

This detail is important because it allows for the definition of a lifting
into the reactive monad that is polymorphic across request and response types.

Note that the model allows trace stutters, i.e. there may be some undetermined
number of steps during which no messages are exchanged, and thus the global
state of the system remains unchanged.

These definitions give us monadic types for the two roles:

> type Client a = Role Req' Rsp' (StateT Stamp Id) a
> type Server a = Role Rsp' Req' (StateT Stamp Id) a

The server's responses are the client's requests, and vice versa.
These definitions allow for a very simple specification of server and client
behaviors as actions in their own respective reactive resumption monads.

Each role maintains its own indendependent message counter in a state layer
of the monad; this is used for sequencing messages in the usual way.

A tick of the counter is just a straightforward state action:

> stamp :: StateT Stamp Id Stamp
> stamp = get >>= \n -> put (n + 1) >> return n

We now have all the parts necessary for a simple but complete monadic model
capapble of specifying the distributed behaviors of the client and server,
according to the simple request-reply protocol.

The client can be factored into its initial query, and a loop that retries
until success:

> client :: Client Rsp
> client  = query >>= \p ->
>           step_Re get >>= \n -> 
>           if (reply n p)
>           then (return p)
>           else (dountil (\p -> reply n p) retry)

> query :: Client Rsp
> query = step_Re stamp >>= \n -> send (Query n)

> retry :: Client Rsp
> retry = step_Re stamp >>= \n -> send (Retry n)

> reply :: Stamp -> Rsp -> Bool
> reply n p = case p of
>               Msg (Reply n') -> if n == n' then True else False
>               _              -> False



Viewed another way, 'client' expresses a simple context-free grammar for the
permissible outgoing message sequences from a client as defined by the
protocol:

  C ::= query Q
  Q ::= retry Q | listen Q | \0

The server behaviors reflect the simplicity of the client.
The server waits for a request to arrive, and sends back a reply
with a matching sequence stamp.

Since the server maintains its own state, it can cache the sequence stamp
of the last received message and reply with 'fault' in the event of
an out-of-order message.

> server :: Server ()
> server = listen >>= \p ->
>          step_Re get >>= \s ->
>          (
>
>            if (stampof p) == (s + 1)
>            then send (Reply s)
>            else send Fault
>
>          ) >> server

The server returns to its listening state after responding.

As with the client, the server suggests a simple CFG description as well:

  S ::= L
  L ::= listen L | listen A
  A ::= listen L | reply L | fault L

We can now obtain a CFG specifying the set of allowable system traces by
putting together the client and server specifications:

  T ::= C M
  M ::= S C M | S

  C ::= query Q
  Q ::= retry Q | wait Q | \0
  S ::= L
  L ::= listen L | listen A
  A ::= reply L | fault L


The top-level trace production 'T' specifies that communication is always
initiated by the client.  The prodcution 'M' specifies the allowable
interleavings of host actions, in this case, a simple, alternating sequence
of requests from the client and responses from the server, ending in a
response from the server.

In fact, 'T' and 'M' can be directly inferred simply by examining the types
of the monads 'Client' and 'Server', since these exactly specify what messages
will be expected by each participant.

What's needed now is a top-level process to formalize the set of allowable
traces.  The approach we'll use is to factor this process into smaller,
specific handlers that deal with message passing between roles.

First, we will express the stuttering behavior of the system with
two handlers for distinguishing whether a host is performing internal
computations or is awaiting an external reply:

> handle_c p c =
>   case p of
>     Listen -> return c
>     p      -> case c of
>                 P (Working, r) -> step_R (r Working) >>= \c' -> handle_c p c'
>                 P (_, r)       -> step_R (r p)
>                 D _            -> return c

> handle_s q s =
>   case q of
>     Listen -> return s
>     q      -> case s of
>                 P (Working, r) -> step_R (r Working) >>= \s' -> handle_s q s'
>                 P (_, r)       -> step_R (r q)
>                 D _            -> return s

All other signals are expressed as internal choices of the client/server;
this alows a very straightforward definition of the top-level specification:

> toplevel c s =
>   case c of
>     D _      -> return ()
>     P (q, _) -> case s of
>                   P (p, _)  -> handle_c p c >>= \c' ->
>                                handle_s q s >>= \s' ->
>                                toplevel c' s'
>
>                   _         -> toplevel c s


How can this handler be used to prove properties about the protocol?

Give an example.

What distinct properties does this protocol, as specified, have?


-- THE END --
