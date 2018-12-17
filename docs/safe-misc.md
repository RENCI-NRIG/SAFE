# Miscellaneous features

## Dynamic script loading

SAFE allows a trust script to be loaded into an authorization server dynamically. A SAFE server reads the source code of a requested trust script, compiles it, and merges (with needed deduplication) the compiled SAFE constructs (logical templates and guards) into the script that the server currently runs.  SAFE includes two built-in guards for loading scripts: *import* and *importSource*. *import* requests the server to load a trust script specified by a pathname; *importSource* passes in source code via a request argument (a string).  Along with other guards defined in the start script, these loading guards are deployed on the server as REST APIs when SAFE stands up. The usage of import and importSource can be find from these two CURL requests and the server responses:

```
$ curl -H "Content-Type:application/json" -XPOST http://152.3.136.26:7777/import -d  '{ "principal": "princpal010", "otherValues": ["/path/to/safe/safe-apps/multi-principal/fine-grained-linking/geni.slang"]}'

{
  "message": "Import completed"
}

$ curl -H "Content-Type:application/json" -XPOST http://152.3.136.26:7777/importSource -d  '{ "principal": "princpal010", "otherValues": ["defpost postObjectAcl(?ObjectId, ?Property) :- [addObjectAcl(?ObjectId, ?Property)]."]}'

{
  "message": "Import completed"
}
```

## inferSet()

Logical statement sets are immutable. SAFE introduces a built-in *inferSet()* in the scripting layer for automated deduction of statements based on an existing statement set and a user-defined rule set. This enables a number of useful applications, such as naming and *speaksFor*. It also allows compliance check over a dynamic list of properties and query optimization through Datalog materialization.  

Transformation of logic statement sets by inferSet() is dynamic, flexible, and efficient, but at no cost for a need to complicate the underlying logic. inferSet() has two parameters -- a reference to a statement set and a reference to a rule set. Both of them can refer to either a remote set or a local set in the SAFE instance cache. They together constitute a context for statement deduction. Below is an example use of inferSet() in STRONG naming.   At runtime, inferSet() invokes the logic inference engine to deduct all statements using the logical rules. The resulting statements are put in a newly created set whose reference is returned to the caller. Therefore, inferSet() does not make any change to the input logical sets (statement set and rule set), but only generates a result set containing all deducted statements.

```
...
?ScidSet := inferSet(?RulesRef, ?ObjDelToken),
...
```

Next: inferQuerySet()


## SAFE debugging: an exemplary logical proof

     ========================================== SAFE PROOF ========================================
    |                                                                                              |
    |                                                                                              |
    |        EK624CkV-eF-wcA6q0tz3DYy11MqgfI8WbtenuZVyJE: srnNameToID(sub20/sub1/sub2,Et29c        |
    |        7tSAdSffRNkk1J8R_96XM9SmhtoAV6ZO1Hbqko:object000001)                                  |
    |                  ||                                                                          |
    |                  || EK624CkV-eF-wcA6q0tz3DYy11MqgfI8WbtenuZVyJE: srnNameToID(?Name,?S        |
    |                  || cid) :- EK624CkV-eF-wcA6q0tz3DYy11MqgfI8WbtenuZVyJE: splitLast(?N        |
    |                  || ame,?Init,?LastComponent), EK624CkV-eF-wcA6q0tz3DYy11MqgfI8Wbtenu        |
    |                  || ZVyJE: srnNameToID(?Init,?Dir), EK624CkV-eF-wcA6q0tz3DYy11MqgfI8W        |
    |                  || btenuZVyJE: is_nonnum(?DirAuthority,rootPrincipal(?Dir)), ?DirAut        |
    |                  || hority: nameObject(?LastComponent,?Scid,?Dir).                           |
    |                  ||                                                                          |
    |                  || sub20/sub1/sub2=>?Name;    Et29c7tSAdSffRNkk1J8R_96XM9SmhtoAV6ZO1        |
    |                  || Hbqko:object000001=>?Scid;    sub20/sub1=>?Init;    sub2=>?LastCo        |
    |                  || mponent                                                                  |
    |                 \||/                                                                         |
    |                  \/                                                                          |
    |                                                                                              |
    |        EK624CkV-eF-wcA6q0tz3DYy11MqgfI8WbtenuZVyJE: srnNameToID(sub20/sub1,bUo205gB8-        |
    |        MbFjQ7TYYDYuFLo8tqU2aUSrSLjeoq__g:object000001);    EK624CkV-eF-wcA6q0tz3DYy11        |
    |        MqgfI8WbtenuZVyJE: is_nonnum(bUo205gB8-MbFjQ7TYYDYuFLo8tqU2aUSrSLjeoq__g,rootP        |
    |        rincipal(bUo205gB8-MbFjQ7TYYDYuFLo8tqU2aUSrSLjeoq__g:object000001));    bUo205        |
    |        gB8-MbFjQ7TYYDYuFLo8tqU2aUSrSLjeoq__g: nameObject(sub2,Et29c7tSAdSffRNkk1J8R_9        |
    |        6XM9SmhtoAV6ZO1Hbqko:object000001,bUo205gB8-MbFjQ7TYYDYuFLo8tqU2aUSrSLjeoq__g:        |
    |        object000001)                                                                         |
    |                  ||                                                                          |
    |                  || EK624CkV-eF-wcA6q0tz3DYy11MqgfI8WbtenuZVyJE: srnNameToID(?Name,?S        |
    |                  || cid) :- EK624CkV-eF-wcA6q0tz3DYy11MqgfI8WbtenuZVyJE: splitLast(?N        |
    |                  || ame,?Init,?LastComponent), EK624CkV-eF-wcA6q0tz3DYy11MqgfI8Wbtenu        |
    |                  || ZVyJE: srnNameToID(?Init,?Dir), EK624CkV-eF-wcA6q0tz3DYy11MqgfI8W        |
    |                  || btenuZVyJE: is_nonnum(?DirAuthority,rootPrincipal(?Dir)), ?DirAut        |
    |                  || hority: nameObject(?LastComponent,?Scid,?Dir).                           |
    |                  ||                                                                          |
    |                  || sub20/sub1=>?Name;    bUo205gB8-MbFjQ7TYYDYuFLo8tqU2aUSrSLjeoq__g        |
    |                  || :object000001=>?Scid;    sub20=>?Init;    sub1=>?LastComponent           |
    |                 \||/                                                                         |
    |                  \/                                                                          |
    |                                                                                              |
    |        EK624CkV-eF-wcA6q0tz3DYy11MqgfI8WbtenuZVyJE: srnNameToID(sub20,lZfcr5mhhY7MKyu        |
    |        5uGauxzszdUFAupms2kwa-Ceb0ww:object000001);    EK624CkV-eF-wcA6q0tz3DYy11MqgfI        |
    |        8WbtenuZVyJE: is_nonnum(lZfcr5mhhY7MKyu5uGauxzszdUFAupms2kwa-Ceb0ww,rootPrinci        |
    |        pal(lZfcr5mhhY7MKyu5uGauxzszdUFAupms2kwa-Ceb0ww:object000001));    lZfcr5mhhY7        |
    |        MKyu5uGauxzszdUFAupms2kwa-Ceb0ww: nameObject(sub1,bUo205gB8-MbFjQ7TYYDYuFLo8tq        |
    |        U2aUSrSLjeoq__g:object000001,lZfcr5mhhY7MKyu5uGauxzszdUFAupms2kwa-Ceb0ww:objec        |
    |        t000001);    EK624CkV-eF-wcA6q0tz3DYy11MqgfI8WbtenuZVyJE: is_nonnum(bUo205gB8-        |
    |        MbFjQ7TYYDYuFLo8tqU2aUSrSLjeoq__g,rootPrincipal(bUo205gB8-MbFjQ7TYYDYuFLo8tqU2        |
    |        aUSrSLjeoq__g:object000001));    bUo205gB8-MbFjQ7TYYDYuFLo8tqU2aUSrSLjeoq__g:         |
    |        nameObject(sub2,Et29c7tSAdSffRNkk1J8R_96XM9SmhtoAV6ZO1Hbqko:object000001,bUo20        |
    |        5gB8-MbFjQ7TYYDYuFLo8tqU2aUSrSLjeoq__g:object000001)                                  |
    |                  ||                                                                          |
    |                  || EK624CkV-eF-wcA6q0tz3DYy11MqgfI8WbtenuZVyJE: srnNameToID(?Name,?S        |
    |                  || cid) :- EK624CkV-eF-wcA6q0tz3DYy11MqgfI8WbtenuZVyJE: singleCompon        |
    |                  || ent(?Name), EK624CkV-eF-wcA6q0tz3DYy11MqgfI8WbtenuZVyJE: is_nonnu        |
    |                  || m(?RootAuthority,rootPrincipal(_Multe5KNgvw3Wk6eYF7_ZVXMXnKwxsTFN        |
    |                  || IzWiY87hM:root)), ?RootAuthority: nameObject(?Name,?Scid,_Multe5K        |
    |                  || Ngvw3Wk6eYF7_ZVXMXnKwxsTFNIzWiY87hM:root).                               |
    |                  ||                                                                          |
    |                  || sub20=>?Name;    lZfcr5mhhY7MKyu5uGauxzszdUFAupms2kwa-Ceb0ww:obje        |
    |                  || ct000001=>?Scid;    _Multe5KNgvw3Wk6eYF7_ZVXMXnKwxsTFNIzWiY87hM=>        |
    |                  || ?RootAuthority                                                           |
    |                 \||/                                                                         |
    |                  \/                                                                          |
    |                                                                                              |
    |        _Multe5KNgvw3Wk6eYF7_ZVXMXnKwxsTFNIzWiY87hM: nameObject(sub20,lZfcr5mhhY7MKyu5        |
    |        uGauxzszdUFAupms2kwa-Ceb0ww:object000001,_Multe5KNgvw3Wk6eYF7_ZVXMXnKwxsTFNIzW        |
    |        iY87hM:root);    EK624CkV-eF-wcA6q0tz3DYy11MqgfI8WbtenuZVyJE: is_nonnum(lZfcr5        |
    |        mhhY7MKyu5uGauxzszdUFAupms2kwa-Ceb0ww,rootPrincipal(lZfcr5mhhY7MKyu5uGauxzszdU        |
    |        FAupms2kwa-Ceb0ww:object000001));    lZfcr5mhhY7MKyu5uGauxzszdUFAupms2kwa-Ceb0        |
    |        ww: nameObject(sub1,bUo205gB8-MbFjQ7TYYDYuFLo8tqU2aUSrSLjeoq__g:object000001,l        |
    |        Zfcr5mhhY7MKyu5uGauxzszdUFAupms2kwa-Ceb0ww:object000001);    EK624CkV-eF-wcA6q        |
    |        0tz3DYy11MqgfI8WbtenuZVyJE: is_nonnum(bUo205gB8-MbFjQ7TYYDYuFLo8tqU2aUSrSLjeoq        |
    |        __g,rootPrincipal(bUo205gB8-MbFjQ7TYYDYuFLo8tqU2aUSrSLjeoq__g:object000001));         |
    |           bUo205gB8-MbFjQ7TYYDYuFLo8tqU2aUSrSLjeoq__g: nameObject(sub2,Et29c7tSAdSffR        |
    |        Nkk1J8R_96XM9SmhtoAV6ZO1Hbqko:object000001,bUo205gB8-MbFjQ7TYYDYuFLo8tqU2aUSrS        |
    |        Ljeoq__g:object000001)                                                                |
    |                  ||                                                                          |
    |                  || _Multe5KNgvw3Wk6eYF7_ZVXMXnKwxsTFNIzWiY87hM: nameObject(sub20,lZf        |
    |                  || cr5mhhY7MKyu5uGauxzszdUFAupms2kwa-Ceb0ww:object000001,_Multe5KNgv        |
    |                  || w3Wk6eYF7_ZVXMXnKwxsTFNIzWiY87hM:root).                                  |
    |                  ||                                                                          |
    |                  || lZfcr5mhhY7MKyu5uGauxzszdUFAupms2kwa-Ceb0ww:object000001=>?Dir;          |
    |                  ||   lZfcr5mhhY7MKyu5uGauxzszdUFAupms2kwa-Ceb0ww=>?DirAuthority             |
    |                 \||/                                                                         |
    |                  \/                                                                          |
    |                                                                                              |
    |        lZfcr5mhhY7MKyu5uGauxzszdUFAupms2kwa-Ceb0ww: nameObject(sub1,bUo205gB8-MbFjQ7T        |
    |        YYDYuFLo8tqU2aUSrSLjeoq__g:object000001,lZfcr5mhhY7MKyu5uGauxzszdUFAupms2kwa-C        |
    |        eb0ww:object000001);    EK624CkV-eF-wcA6q0tz3DYy11MqgfI8WbtenuZVyJE: is_nonnum        |
    |        (bUo205gB8-MbFjQ7TYYDYuFLo8tqU2aUSrSLjeoq__g,rootPrincipal(bUo205gB8-MbFjQ7TYY        |
    |        DYuFLo8tqU2aUSrSLjeoq__g:object000001));    bUo205gB8-MbFjQ7TYYDYuFLo8tqU2aUSr        |
    |        SLjeoq__g: nameObject(sub2,Et29c7tSAdSffRNkk1J8R_96XM9SmhtoAV6ZO1Hbqko:object0        |
    |        00001,bUo205gB8-MbFjQ7TYYDYuFLo8tqU2aUSrSLjeoq__g:object000001)                       |
    |                  ||                                                                          |
    |                  || lZfcr5mhhY7MKyu5uGauxzszdUFAupms2kwa-Ceb0ww: nameObject(sub1,bUo2        |
    |                  || 05gB8-MbFjQ7TYYDYuFLo8tqU2aUSrSLjeoq__g:object000001,lZfcr5mhhY7M        |
    |                  || Kyu5uGauxzszdUFAupms2kwa-Ceb0ww:object000001).                           |
    |                  ||                                                                          |
    |                  || bUo205gB8-MbFjQ7TYYDYuFLo8tqU2aUSrSLjeoq__g:object000001=>?Dir;          |
    |                  ||   bUo205gB8-MbFjQ7TYYDYuFLo8tqU2aUSrSLjeoq__g=>?DirAuthority             |
    |                 \||/                                                                         |
    |                  \/                                                                          |
    |                                                                                              |
    |        bUo205gB8-MbFjQ7TYYDYuFLo8tqU2aUSrSLjeoq__g: nameObject(sub2,Et29c7tSAdSffRNkk        |
    |        1J8R_96XM9SmhtoAV6ZO1Hbqko:object000001,bUo205gB8-MbFjQ7TYYDYuFLo8tqU2aUSrSLje        |
    |        oq__g:object000001)                                                                   |
    |                  ||                                                                          |
    |                  || bUo205gB8-MbFjQ7TYYDYuFLo8tqU2aUSrSLjeoq__g: nameObject(sub2,Et29        |
    |                  || c7tSAdSffRNkk1J8R_96XM9SmhtoAV6ZO1Hbqko:object000001,bUo205gB8-Mb        |
    |                  || FjQ7TYYDYuFLo8tqU2aUSrSLjeoq__g:object000001).                           |
    |                  ||                                                                          |
    |                 \||/                                                                         |
    |                  \/                                                                          |
    |                                                                                              |
    |                  {}                                                                          |
    |                                                                                              |
     ========================================= END OF PROOF =======================================