require import AllCore Int Real NewFMap FSet Distr DBool.
(*require import DiffieHellman PKS PKE SymmetricEncryption.*)
require (*  *) CyclicGroup.
clone export CyclicGroup as G.

(*----------------------------theory STS----------------------------*)

type pkey = group.
type skey = F.t. 
type message = group * group. (*g^x, g^y*)
type sharedkey = group. 
type signature = skey * message.
(*type plaintext.*)
type ciphertext. 

module type STS_Infrastructure ={
  proc keygen():pkey
  proc sign(sk:skey, m: message): signature
  proc verify(pk:pkey, m:message, s: signature): bool
  proc enc(shk:sharedkey, s:signature): ciphertext
  proc dec(shk:sharedkey, c:ciphertext): signature
}.

module type STS_Adversary(I:STS_Infrastructure) = {
  proc * init(): unit {}
  proc step1_receive(pk:pkey): group
  proc step1_send(): group
  proc step2_receive(pk:pkey, c:ciphertext): group * ciphertext
  proc step2_send(): group * ciphertext 
  proc step3_receive(c:ciphertext): ciphertext
  proc step3_send(): ciphertext
  proc step4_guess(): group 
}.
(* Game*)
module Game (I:STS_Infrastructure, A:STS_Adversary) = {

  module A = A(I)

  proc main():bool = {
  var x, y;
  var k,k': group;  
  var b, b', b'': bool;
  var alpha', alpha'',beta', beta'':pkey;  
  var sign_a, sign_a',sign_b, sign_b':signature;
  var sigma_a, sigma_b:ciphertext;
  (*Step 1*)
   A.init();
   x = $FDistr.dt;
   alpha' = g^x; 
   A.step1_receive(alpha');
   alpha''=A.step1_send();
    
   (*Step 2*)   
   y = $FDistr.dt;
   beta' = g^y; 
   sign_b = I.sign(y, (alpha'',beta'));
   sigma_b = I.enc((alpha'')^y, sign_b); 
   A.step2_receive(beta', sigma_b);
   (beta'', sigma_b) = A.step2_send();

     (*Step 3*)
   sign_b'=I.dec(beta''^x, sigma_b);
   b = I.verify(beta'', (alpha'', beta'), sign_b') ; (*???*)
   sign_a = I.sign(x, (alpha'',beta')); 
   sigma_a = I.enc((beta'')^x,sign_a);
   A.step3_receive(sigma_a);(* A(I).step3_receive(sigma_a) = A.step3_send();*)
   sigma_a = A.step3_send();

     (*step 4*)
   sign_a'= I.dec(alpha''^y, sigma_a);
   b'= I.verify(alpha'', (alpha'', beta'),sign_a');

   (*Win TODD*)
   b'' = beta''^x <> alpha''^y;
   k = A.step4_guess();
  
     return k = g^(x*y) \/ b'';
  }
}.
