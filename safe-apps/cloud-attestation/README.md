# Latte Kubernetes (L-Kube)

The L-Kube documentation illustrates scenarios for creating, checking,
and using attestations of services running in pods launched from Latte Kubernetes.
It explains how code and configuration of a pod are attested through
Latte, how properties of a pod service are drawn based on endorsements
and policies of involved parties, and how L-Kube can be integrated to enable
attestation-based access control in applications, e.g., joint data
analytics. 

## Latte Slang scripts
The [Latte Slang script] (https://github.com/jerryz920/SAFE-latte/blob/yan/latte/safe-apps/cloud-attestation/new/latte.slang)
imports [plist library] (https://github.com/jerryz920/SAFE-latte/blob/yan/latte/safe-apps/cloud-attestation/plist-lib.slang)
and [Latte policy Slang] (https://github.com/jerryz920/SAFE-latte/blob/yan/latte/safe-apps/cloud-attestation/new/policy.slang).
These Slang scripts provide a variety of constructs for attesting Latte instances
(e.g., VMs and pods), endorsing code properties (e.g., attester) and trusted endorsers,
and checking policy compilance to guard service access. A common set of
latte policy rules provided in the scripts allows re-use to check configurations
and properties attested by instances which themselves are attested.
The following section walks through a typical process of
attesting, endorsing, and checking in Latte using an end-to-end running example.
In this example, a test uses a bash shell [script]
(https://github.com/jerryz920/SAFE-latte/blob/yan/latte/safe-apps/cloud-attestation/new/test_app_policy.sh) 
for invoking a Latte construct. 
  

## Attesting Latte instances
We use Latte to attest a k8s pod and the environment in
which the k8s pod runs. As a result, attestations and endorsements
start from the IaaS layer and extend to the layer of k8s. 

### Start a Kubernetes cluster
When an IaaS launches a Kubernetes cluster, it runs a kubernetes
master in a VM and attests to the kube image that this master
runs. The attestation can also include statements about the network
address of this VM and the range of IP addresses allocated for
pods on the k8s cluster. In this example, the k8s master belongs to a
VPC (i.e., vpc-1), uses an IP address
172.16.0.2 and a port range 0-65535, and is assigned an IP range (CIDR)
192.168.2.0/24 for pods to be launched from it.

```
postVMInstance $IAAS kmaster kube-image vpc-1 172.16.0.2:0-65535 192.168.2.0/24
```

### Create a pod on the k8s cluster

On creation of a new pod, k8s master attests to the network
address and the manifest
of this pod. Network address attested by k8s master is comprised of two
components: an IP address and a port range. In this example, pod1 is on
IP address 192.168.2.1 and owns a port range 0-65535; pod6 is on 
IP address 192.168.2.6 and owns the same port range as pod1 does. 
An attestation of a pod also includes attestation of each container
inside this pod, and the configuration
of the image with which the container runs. The *image configuration* 
associated to a running container is captured in an attestation using 
a *list* of configuration key-value tuples which
themselves are also represented as lists. 

<!--  ``$IAAS'' uses an environment
variable holding the ID of the IAAS underneath.
-->

```
postInstance kmaster $IAAS pod1 imagenotused 192.168.2.1:0-65535
postInstanceConfigList kmaster pod1 containers '[ctn1,ctn2]'
postInstanceConfigList kmaster pod1 global '[ctn1,ctn2]'
postInstanceConfigList kmaster pod1 ctn1 '[image_c1,[k1,v1],[k2,v2]]'
postInstanceConfigList kmaster pod1 ctn2 '[image_c2,[k3,v3],[k4,v4]]'
```

```
postInstance kmaster $IAAS pod6 imagenotused 192.168.2.6:0-65535
postInstanceConfigList kmaster pod6 containers '[ctn1,ctn2]'
postInstanceConfigList kmaster pod6 global '[ctn1,ctn2]'
postInstanceConfigList kmaster pod6 ctn1 '[image_c1,[k1,v6],[k2,v7],[k4,v4]]'
postInstanceConfigList kmaster pod6 ctn2 '[image_c2,[k1,v1],[k4,v5]]'
```

## Endorsing
Latte allows endorsements on image properties, configuration properties, and
the endorsers themselves. 

### VM image properties
One can endorse certain properties of images based on the code. 
For example, with the following commands Bob 
endorses on the property of *attester* for kube-image that kmaster runs. 
Bob then stores the link to this endorsement into his *trust hub*.

```
postEndorsement bob kube-image attester 1
postEndorsementLink bob kube-image
```

### Use of endorsements
A principal can make use of an image endorsement by incorporating this
endorsement along with a declaration of the speaker as a trusted endorser. This is accomplished via logic-set
linking of SAFE. The principal can choose to link an interested endorsement 
(or a trust hub) to a set of its own for an endorser policy which
specifies  whose endorsements it trusts and on what endorsable property.
For instance, Alice can optionally accept Bob's endorsements on the
property *attester*. Of course, Bob accepts the endorsements made by itself. 

```
postTrustedEndorser alice bob attester
postTrustedEndorser bob bob attester
``` 

### Property lists for configurations

An authorization policy asserts certain properties for images
and their configurations. An authorizer may only
accept images from a vetted whitelist, and may not allow an image configured
in an arbitrary way. For example, safety-sensitive configuration
must be unset, set, or set in particular ways, depending on application
context. Latte provides  mechanics to support checks on a common set of configuration properties.
It uses *property lists*, a predicated list representation of configuration using properties,
to faciliate expression, interpretation, and evaluation
for three categories of properties: *prohibited*, *required*, and *qualifier*.
These three properties are used to denote configurations that must not be present,
must be present, and must be specified in a certain way, respectively. 
In this example, Alice accrues the specifications for policy1, publishing what are
acceptable container images, and for each image what are the prohibited 
configuration (by keys), the required configuration (by
keys), and the qualifier configuration 
(by key-value tuples). Note that prohibited, required, and qualifier configurations are 
all property lists.

```
postImagePolicy alice policy1 "[image_c1,image_c2,image_c3]"
postProhibitedPolicy alice policy1 "[image_c1,k5]"
postProhibitedPolicy alice policy1 "[image_c2,k5]"
postRequiredPolicy alice policy1 "[image_c1,k1,k2]"
postRequiredPolicy alice policy1 "[image_c2,k1]"
postQualifierPolicy alice policy1 "[image_c1,[k4,v4]]"
postQualifierPolicy alice policy1 "[image_c2,[k1,v1]]"
```

## Authorizing
An authorizor invokes a Latte guard in Slang to check if 
related attestations, configurations, and endorsements of a requester
together meet the specification of a particular policy before it
grants access or allocates resources
to the requester. 

### Checking for access control
In joint data analytics, a storage guard uses a Latte client
to check policy compliance on the arrival of
an access request. Authorization checks by Latte ensure that not only the 
code and configuration of the requester but also the underlying execution 
environment where the
requester resides all comply with the guard's policy. The command below
issues for Alice a request to check pod6 against policy1. This authorization
check will pass.

```
checkPodByPolicy alice kmaster pod6 policy1
```


### Adopting an existing policy

Alternatively, a principal in Latte can simply adopt an existing policy to 
guard its service. For example, Bob might have set up another policy as shown
by the commands below. 

```
postImagePolicy bob policy1 "[image_c1,image_c2]"
postProhibitedPolicy bob policy1 "[image_c1,k5]"
postProhibitedPolicy bob policy1 "[image_c2,k5]"
postQualifierPolicy bob policy1 "[image_c1,[k1,v1]]"
postQualifierPolicy bob policy1 "[image_c2,[k4,v4]]"
postRequiredPolicy bob policy1 "[image_c1,k1,k2]"
postRequiredPolicy bob policy1 "[image_c2,k3]"
```

Alice adopts Bob's policy by endorsing Bob as a trusted policy source. Note that 
here it uses SAFE's *direct linking* to incorporate the desired policy into this
endorsement of trusted endorser. This linking structure prunes the inference context at authorization time
and can dramatically reduce resource consumption (e.g., memory footprint), 
and delay of property proving on the authorizer.

 
```
postAndDLinkTrustedEndorser alice bob trustPolicy endorsements/trustPolicy/policy1
```


Now, Alice can check a pod, e.g., pod1, using this policy. While it previously has failed, 
this check passes. 

```
checkPodByPolicy alice kmaster pod1 policy1
```