# SAFE primer using Strong policy framework

## Overview

The Strong policy framework permits set-based resource ownership with delegations over namespaces. The policy definition is located [here](../safe-apps/strong).

## Tutorial steps

Ensure the SAFE docker entry point is just a shell (not starting a SAFE server), we will be using a CLI.

Generate 10 keys with prefix 'strong-' in principalkeys/ directory under dockerfiles/:
```
$ cd dockerfiles
$ mkdir principalkeys
$ bash ../utility/safe_keygen.sh strong- 10 principalkeys
```

Using docker-compose will properly mount the volumes needed by the SAFE container.

Build and start the Riak and SAFE containers:
```
$ cd dockerfiles
$ docker-compose build
$ docker-compose up
```

slang>import("/imports/strong-client.slang").

strong-1@slang> ?ServerJVM := "localhost:7777".
strong-1@slang> ?P1 := postIdSetRaw("strong-1").
strong-1@slang> ?Self := "strong-2".
strong-2@slang> ?P2 := postIdSetRaw("strong-2").
strong-2@slang> ?Self := "strong-3".
strong-3@slang> ?P3 := postIdSetRaw("strong-3").
strong-3@slang> ?Self := "strong-4".
strong-4@slang> ?P4 := postIdSetRaw("strong-4").
strong-4@slang> ?Self := "strong-5".
strong-5@slang> ?P5 := postIdSetRaw("strong-5").
strong-5@slang> ?UUID1 := "6ec7211c-caaf-4e00-ad36-0cd413accc91".
strong-5@slang> ?UUID2 := "1b924687-a317-4bd7-a54f-a5a0151f49d3".
strong-5@slang> ?UUID3 := "26dbc728-3c8d-4433-9c4b-2e065b644db5".
strong-5@slang> ?UUID4 := "1ef7e6dd-5342-414e-8cce-54e55b3b9a83".

strong-5@slang> delegateName("project00", $P1, $UUID1, $P2, $UUID2)?
xHjlQ-vLQREF5uwmNw4NdQPHt-TWKEKwo_oTqwtkCj0=@slang> delegateName("dataset00", $P2, $UUID2, $P3, $UUID3)?
H3RFFi8NYRUlAa9wQTPgFzW4RqicobTcdsxnWLxn9S8=@slang> delegateName("part00", $P3, $UUID3, $P4, $UUID4)?

TJD9gT4DC4VQXdWNNiIB7MJlAlzqbqCatZ2vO-7Y3Kw=@slang> queryName("$P1:$UUID1", "project00/dataset00/part00")?

H3RFFi8NYRUlAa9wQTPgFzW4RqicobTcdsxnWLxn9S8=@slang> ?Self := $P3.

P3@slang> postDirectoryAccess("$P5:group0", "$P3:$UUID3")?

slang> ?Self := $P5.
hD_uYbm1ivhX_5Ph5C08_A1MvCAVZfvQq128BQuXjYA=@slang> ?Membership := postGroupMember("$P5:group0", $P5, "true")?
hD_uYbm1ivhX_5Ph5C08_A1MvCAVZfvQq128BQuXjYA=@slang> ?SubjectSet := updateSubjectSet($Membership).

hD_uYbm1ivhX_5Ph5C08_A1MvCAVZfvQq128BQuXjYA=@slang> ?ReqEnvs := ":::$SubjectSet".
hD_uYbm1ivhX_5Ph5C08_A1MvCAVZfvQq128BQuXjYA=@slang> ?Self := $P4.
TJD9gT4DC4VQXdWNNiIB7MJlAlzqbqCatZ2vO-7Y3Kw=@slang> accessNamedObject($P5, "project00/dataset00", "$P1:$UUID1")?
[satisfied]
TJD9gT4DC4VQXdWNNiIB7MJlAlzqbqCatZ2vO-7Y3Kw=@slang> accessNamedObject($P5, "project00/dataset00/part00", "$P1:$UUID1")?
[satisfied]
TJD9gT4DC4VQXdWNNiIB7MJlAlzqbqCatZ2vO-7Y3Kw=@slang> accessNamedObject($P5, "project00", "$P1:$UUID1")?
[unsatisfied]
~