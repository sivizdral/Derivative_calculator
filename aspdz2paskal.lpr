program aspdz2paskal;
uses math;
//skup svih karaktera koji se mogu javiti u stablu
const
  dozvoljeni = ['l','e','a','A'..'Z','+','-','*','/','^','n','u','0','1'];
type
  pokCvor = ^cvor;
  cvor = record
    levi:pokCvor;
    desni:pokCvor;
    oznaka:char;
  end;
//pokcvor = element stabla, pokelem = element steka za skladistenje cvorova
  pokElem = ^elem;
  elem = record
    info:pokCvor;
    sled:pokElem;
  end;
//pokreal = element steka za skladistenje vrednosti pri racunanju
  pokreal = ^br;
  br = record
    info:real;
    sled:pokreal;
  end;
//niz za pamcenje vrednosti promenljivih pri racunanju
  niz = array [1..26] of real;
var
  koren, drugi, treci, difrezultat, difprethodni, kopija, sredjen: pokCvor;
  odg, neg:boolean;
  ulaz, a, i, brojizvoda, podizbor: integer;
  red, izraz: string;
  prom, dif: char;
  rezultat: real;
  vrednosti: niz;
//push, empty, pop, top = za rad sa stekom za cvorove
//sa prefiksom rac = za rad sa stekom za vrednosti
procedure push(var s:pokElem;var x:pokCvor);
var
  p:pokElem;
begin
  new(p);
  p^.info:=x;
  p^.sled:=s;
  s:=p;
end;
procedure empty(var s:pokElem;var ans:boolean);
begin
  if s=nil then ans:=true
    else ans:=false;
end;
procedure pop(var s:pokElem;var x:pokCvor);
var
  ans:boolean;p:pokElem;
begin
  empty(s,ans);
  if not ans then begin
    p:=s;
    s:=p^.sled;
    x:=p^.info;
    dispose(p);
end;
end;
procedure top(var s:pokElem; var x:pokCvor);
begin
  x:=s^.info;
end;
procedure racpush(var s:pokreal;var x:real);
var
  p:pokreal;
begin
  new(p);
  p^.info:=x;
  p^.sled:=s;
  s:=p;
end;
procedure racempty(var s:pokreal;var ans:boolean);
begin
  if s=nil then ans:=true
    else ans:=false;
end;
procedure racpop(var s:pokreal;var x:real);
var
  ans:boolean;p:pokreal;
begin
  racempty(s,ans);
  if not ans then begin
    p:=s;
    s:=p^.sled;
    x:=p^.info;
    dispose(p);
end;
end;
//ipr vraca prioritet pri unosu - pomocna funkcija pri pravljenju stabla
function ipr(c: char):integer;
var i:integer;
begin
  if ((c='+') or (c='-')) then i:=2;
  if ((c='*') or (c='/')) then i:=3;
  if (c='^') then i:=5;
  if (c=')') then i:=1;
  if (c='(') then i:=7;
  if ((c='l') or (c='a') or (c='e') or (c='u')) then i:=6;
  ipr:=i;
end;
//spr vraca prioritet na steku - pomocna funkcija pri pravljenju stabla
//najvise prioritete imaju log, abs, exp i unarni minus - 6
//stepenovanje ima ipr 5, a spr 4, jer je sa desna na levo grupisanje
//* i / imaju 3, a + i - imaju 2
function spr(c: char):integer;
var i:integer;
begin
  if ((c='+') or (c='-')) then i:=2;
  if ((c='*') or (c='/')) then i:=3;
  if (c='^') then i:=4;
  if (c='(') then i:=0;
  if ((c='l') or (c='a') or (c='e') or (c='u')) then i:=6;
  spr:=i;
end;
//funkcija vraca napravljen cvor od datog karaktera
function napravicvor(c: char):pokCvor;
var
  novi:pokCvor;
begin
  new(novi);
  novi^.oznaka:=c;
  novi^.levi:=nil;
  novi^.desni:=nil;
  napravicvor:=novi;
end;
//funkcija ispituje da li je funkcija data karakterom binarna ili ne (unarna)
function binarna(c: char):boolean;
begin
  if ((c='+') or (c='-') or (c='*') or (c='/') or (c='^') or (c='l')) then binarna:=true
  else binarna:=false;
end;
//funkcija vrsi povezivanje cvorova na taj nacin sto ih uzima sa steka onoliko
//koliko treba u zavisnosti od funkcije a zatim vraca dobijeni povezani cvor na stek
procedure povezi(var lista: pokElem; var novi: pokCvor);
begin
  if binarna(novi^.oznaka) then begin
    pop(lista, novi^.desni);
    pop(lista, novi^.levi);
  end
  else pop(lista, novi^.levi);
  push(lista, novi);
end;
{funkcija radi po slicnom principu kao in2post algoritam, s razlikom u tome sto
ona ne pravi postfiksni izraz vec stablo direktno iz infiksnog oblika tako sto
operande odmah pretvara u cvorove i redja ih na stek za operande, a operatore pretvara
u cvorove i redja na stek za operatore; kada dodje red na neku operaciju da se
skine sa steka, koristi se prethodna funkcija da je poveze sa svoja dva operanda}
procedure pravistablo(var koren: pokCvor; var izraz:string);
var
  stek, opstek: pokElem; i, br1, br2:integer; novi: pokCvor; ans: boolean;
begin
  stek:=nil;
  opstek:=nil;
  i:=1;
  while i<=length(izraz) do
  begin
    if (izraz[i]='-') and (izraz[i-1]='(') then izraz[i]:='u';
    if ((ord(izraz[i])>=ord('A')) and (ord(izraz[i])<=ord('Z'))) then
    begin
      novi:=napravicvor(izraz[i]);
      push(stek, novi);
    end
    else if (izraz[i]<>',') then
    begin
      empty(opstek, ans);
      br1:=ipr(izraz[i]);
      if (not ans) then
      begin
      top(opstek, novi);
      br2:=spr(novi^.oznaka);
      end;
      while (not ans) and (br1<=br2) do
      begin
        pop(opstek, novi);
        povezi(stek, novi);
        empty(opstek, ans);
        if (not ans) then
        begin
        top(opstek, novi);
        br2:=spr(novi^.oznaka);
        end;
      end;
      if (izraz[i]<>')') then
      begin
        novi:=napravicvor(izraz[i]);
        push(opstek, novi);
      end
      else pop(opstek, novi);
    end;
    if ((izraz[i]='l') or (izraz[i]='a') or (izraz[i]='e')) then i:=i+2;
    i:=i+1;
  end;
  empty(opstek, ans);
  while (not ans) do
  begin
    pop(opstek, novi);
    povezi(stek, novi);
    empty(opstek, ans);
  end;
  pop(stek, koren);
end;
{funkcija sluzi da garantuje korektan ispis pri prefiksom ispisu iz stabla, jer
unutar stabla se sve funkcije pamte jednim karakterom, sto korisnik ne bi trebalo
da primeti - treba ih ispisati onako kako su i unete}
procedure proc(var x:pokCvor);
var
  c: char;
begin
  c:=x^.oznaka;
  if (c='l') then write('log')
  else if (c='a') then write('abs')
  else if (c='e') then write('exp')
  else if (c='u') then write('-')
  else if (c='n') then write('ln')
  else write(c);
end;
{funkcija ide preorder obilaskom po stablu i redom ispisuje sadrzaj cvorova; na
ovaj nacin se direktno dobija prefiksni oblik izraza, jer se prvo ispise koren u
kome je operator, pa tek onda operandi ili podizrazi}
procedure preorder(var koren: pokCvor);
var
  novi: pokCvor; stek: pokElem; ans: boolean;
begin
  stek:=nil;
  push(stek, koren);
  empty(stek, ans);
  while (not ans) do
  begin
    pop(stek, novi);
    while (novi<>nil) do
    begin
      proc(novi);
      if (novi^.desni<>nil) then push(stek, novi^.desni);
      novi:=novi^.levi;
    end;
    empty(stek, ans);
  end;
end;
{funkcija opet koristi preorder nacin obilaska; potrebna su zato dva steka -
jedan za preorder obliazak, a drugi za pamcenje nivoa svakog cvora; u zavisnosti
od nivoa ispisuje se ispred sadrzaja cvora potreban broj crtica, a zatim sadrzaj
u uglastim zagradama; ovakvim nacinom ispisa obezbedjuje se da se jasno moze u
stablu razlikovati koji je cvor u kakvoj relaciji sa nekim drugim; levi sin je
uvek iznad desnog sina; u slucaju da cvor ima samo jednog sina, nema preskoka vec
se ide dalje po stablu i bice ispisan samo taj jedan sin; ovakav nacin ispisa sam
upotrebio jer je na konsultacijama receno da moze ovako - dobija se kao sa 115.
strane pod b - ispis indentacijom, razlika je samo sto je meni malo obrnuto jer
sam pisao sa leve strane, pa koren ima najmanju indentaciju, sledeci nivo vecu,
sledeci jos vecu itd.; nadam se da deluje pregledno}
procedure ispisstabla(var koren: pokCvor);
var
  novi, cvor: pokCvor; stek, nivostek: pokElem; ans: boolean; i, nivo:integer;
begin
  stek:=nil;
  nivostek:=nil;
  nivo:=-1;
  push(stek, koren);
  cvor:=napravicvor(chr(nivo+1));
  push(nivostek, cvor);
  empty(stek, ans);
  while (not ans) do
  begin
    pop(stek, novi);
    pop(nivostek, cvor);
    nivo:=ord(cvor^.oznaka);
    while (novi<>nil) do
    begin
      nivo:=nivo+1;
      for i:=1 to 4*(nivo-1) do write('-');
      if (novi^.oznaka='l') then writeln('[log]')
      else if (novi^.oznaka='e') then writeln('[exp]')
      else if (novi^.oznaka='a') then writeln('[abs]')
      else if (novi^.oznaka='n') then writeln('[ln]')
      else if (novi^.oznaka='u') then writeln('[-]')
      else writeln('[', novi^.oznaka,']');
      if (novi^.desni<>nil) then
      begin
      push(stek, novi^.desni);
      cvor:=napravicvor(chr(nivo));
      push(nivostek, cvor);
      end;
      novi:=novi^.levi;
    end;
    empty(stek, ans);
  end;
end;
{funckije pomrsikonce i razmrsikonce su bile kreativan nacin da pri postorder
obilasku stabla umesto pamcenja indikatora za koji nisam ostavio prostor unutar
cvora stabla nadjem neki nacin da odredim da li je cvor vec jednom obidjen ili ne;
princip je sledeci: ako cvor nije obidjen, onda ce se njegov karakter naci u dozvo-
ljenim znacima, pa je potrebno nekako ga izvrnuti da bi jasno pokazao da je obidjen
sto se radi u funkciji pomrsikonce, gde se on po ascii tabeli salje u nedozvoljene
karaktere; kada se drugi put obidje cvor, indikator je da njegov karakter nije u
dozvoljenim znacima, te ga treba vratiti u dozvoljene po istom samo obrnutom principu
funkcijom razmrsikonce da bi se sa njim mogle vrsiti operacije; svuda gde se koristi
postorder ove dve funkcije sluze kao zamena za indikator}
procedure pomrsikonce(var cvor:pokCvor);
var
  c:char;
begin
  c:=cvor^.oznaka;
  if (c='l') or (c='e') or (c='a') or (c='^') or (c='n') or (c='u') then c:=chr(ord(c)+1);
  if (ord(c)>=ord('A')) and (ord(c)<=ord('Z')) then c:=chr(ord(c)-51);
  if (ord(c)>=ord('(')) and (ord(c)<=ord('1')) then c:=chr(ord(c)+11);
  cvor^.oznaka:=c;
end;
procedure razmrsikonce(var cvor:pokCvor);
var
  c:char;
begin
  c:=cvor^.oznaka;
  if (c='m') or (c='f') or (c='b') or (c='_') or (c='o') or (c='v') then c:=chr(ord(c)-1);
  if (ord(c)>=14) and (ord(c)<=39) then c:=chr(ord(c)+51);
  if (ord(c)>=51) and (ord(c)<=60) then c:=chr(ord(c)-11);
  cvor^.oznaka:=c;
end;
{funkcija za racunanje ima prosledjen niz vrednosti koje se unose u meniju i pomocu
kojih racuna vrednost celokupnog izraza tako sto se stablo obidje postorder, pri
dolasku na operand na stek za racunanje se prosledjuje njegova vrednost iz niza, pri
dolasku na operator se skida 2 ili 1 vrednost sa steka i vrsi se operacija nad
njima, a zatim se dobijeni rezultat prosledjuje na stek za racunanje; konacna vrednost
se dobija kao posledji preostali na steku za racunanje; iako vrednosti pocetnih
promenljivih mogu biti samo celi brojevi, rezultat, zbog operacija kao sto su log
i exp, daje realan broj zaokruzen na dve decimale}
procedure racunanje(var koren: pokCvor; var vrednosti:niz; var rezultat:real);
var
  stek1:pokElem; tekuci, novi: pokCvor; ans:boolean; stek2: pokreal; rez, op1, op2, a:real;
begin
  stek1:=nil;
  stek2:=nil;
  tekuci:=koren;
  while (tekuci<>nil) do
  begin
    push(stek1, tekuci);
    tekuci:=tekuci^.levi;
  end;
  empty(stek1, ans);
  while (not ans) do
  begin
    pop(stek1, novi);
    if (novi^.oznaka in dozvoljeni) then
    begin
    pomrsikonce(novi);
    push(stek1, novi);
    novi:=novi^.desni;
    while (novi<>nil) do
    begin
      push(stek1, novi);
      novi:=novi^.levi;
    end;
    empty(stek1, ans);
    end
    else
    begin
      razmrsikonce(novi);
      if (ord(novi^.oznaka)>=ord('A')) and (ord(novi^.oznaka)<=ord('Z')) then racpush(stek2, vrednosti[ord(novi^.oznaka)-ord('A')+1])
      else if novi^.oznaka='1' then
      begin
        a:=1;
        racpush(stek2, a);
      end
      else if novi^.oznaka='0' then
      begin
        a:=0;
        racpush(stek2, a);
      end
      else if (binarna(novi^.oznaka)) then
      begin
        racpop(stek2, op1);
        racpop(stek2, op2);
        case novi^.oznaka of
          '+': rez:=op1+op2;
          '-': rez:=op2-op1;
          '*': rez:=op1*op2;
          '/': rez:=op2/op1;
          '^': rez:=power(op2, op1);
          'l': rez:=(ln(op1))/(ln(op2));
        end;
        racpush(stek2, rez);
      end
      else begin
        racpop(stek2, op1);
        case novi^.oznaka of
          'a': rez:=abs(op1);
          'e': rez:=exp(op1);
          'n': rez:=ln(op1);
          'u': rez:=-op1;
        end;
        racpush(stek2, rez);
      end;
      empty(stek1, ans);
    end;
  end;
  racpop(stek2, rez);
  rezultat:=rez;
end;
//funkcija proverava da li se u datom podstablu nalazi bilo gde promenljiva po
//kojoj se diferencira izraz
procedure provera(var koren: pokCvor; var odgovor: boolean; var promenljiva: char);
var
  novi: pokCvor; stek: pokElem; ans: boolean;
begin
  odgovor:=false;
  stek:=nil;
  push(stek, koren);
  empty(stek, ans);
  while (not ans) do
  begin
    pop(stek, novi);
    while (novi<>nil) do
    begin
      if novi^.oznaka=promenljiva then odgovor:=true;
      if (novi^.desni<>nil) then push(stek, novi^.desni);
      novi:=novi^.levi;
    end;
    empty(stek, ans);
  end;
end;
//funkcija kopira stablo u drugo stablo koristeci postorder obilazak
procedure kopi(var koren: pokCvor; var novikoren: pokCvor);
var
  stek1, stek2: pokElem;
  novi, tekuci, kopiran, kopiran1, kopiran2: pokCvor; ans: boolean;
begin
  stek1:=nil;
  stek2:=nil;
  tekuci:=koren;
  while (tekuci<>nil) do
  begin
    push(stek1, tekuci);
    tekuci:=tekuci^.levi;
  end;
  empty(stek1, ans);
  while (not ans) do
  begin
    pop(stek1, novi);
    if (novi^.oznaka in dozvoljeni) then
    begin
    pomrsikonce(novi);
    push(stek1, novi);
    novi:=novi^.desni;
    while (novi<>nil) do
    begin
      push(stek1, novi);
      novi:=novi^.levi;
    end;
    empty(stek1, ans);
    end
    else
    begin
      razmrsikonce(novi);
      if ((ord(novi^.oznaka)>=ord('A')) and (ord(novi^.oznaka)<=ord('Z'))) or
      (novi^.oznaka='0') or (novi^.oznaka='1') then
      begin
        kopiran:=napravicvor(novi^.oznaka);
        push(stek2, kopiran);
      end
      else if binarna(novi^.oznaka) then
      begin
        pop(stek2, kopiran1);
        pop(stek2, kopiran2);
        kopiran:=napravicvor(novi^.oznaka);
        kopiran^.levi:=kopiran2;
        kopiran^.desni:=kopiran1;
        push(stek2, kopiran);
      end
      else
      begin
        pop(stek2, kopiran1);
        kopiran:=napravicvor(novi^.oznaka);
        kopiran^.levi:=kopiran1;
        push(stek2, kopiran);
      end;
      empty(stek1, ans);
    end;
   end;
  pop(stek2, novikoren);
end;
{funkcija se krece kroz stablo postorder obilaskom; kada se naidje na operand, on
moze biti onaj koji nam je varijabla po kojoj diferenciramo, u tom slucaju njegov
izvod je 1, inace za bilo koje drugo slovo bice 0; rezultati diferenciranja se
pakuju na stek za izdiferencirana podstabla; kada se naidje na operator, sa ovog
steka se izvlace vrednosti, i zatim uparuju po pravilima za diferenciranje tako
da dobijeno podstablo opet predstavlja dobro izdiferenciran podizraz u opstem
slucaju, i zatim se opet prosledjuje - primer bi bilo A*B stablo a diferencira
se po A - prvo se racuna izvod od A, sto je 1 i gura se na stek, zatim od B sto je
0 i gura se na stek, zatim izvod od f*g je u opstem slucaju f'*g+g'*f, dakle sa
steka sa diferenciranim izrazima se skidaju B'=0 i A'=1, zatim se iz osnovnog
stabla koje se diferencira kopiraju podstabla A i B i zatim se kombinuju tako sto
se prvo napravi cvor +, zatim njegova deca su dva cvora *, a njihova deca prethodno
navedeni podizrazi, cime se dobija:
    *                              +
od A B               dobija se  *     *
                               1 B   0 A
ovako se podstabla uklapaju i na dalje, sve dok se ne dodje do korena; za sve
funkcije koje se mogu naci u izrazu ispisana su opsta pravila diferenciranja;
funkcija obuhvata i slozene izvode odjednom bez upotrebe rekurzije - svaku funkciju
gleda kao slozenu, pa gde je potrebno mnozi sa X' gde je X podizraz koji se
diferencira, a ako se desi da to bude 1, to ce se srediti u funkciji za sredjivanje,
cime se dobija dobro izdiferencirano stablo u svakom slucaju}
procedure diferenciranje(var koren: pokCvor; var rezultat: pokCvor; var dif: char);
var
  stek1, difstek: pokElem; ans, odg: boolean;
  tekuci, novi, difnovi, difprvi, difdrugi, dete1, dete2, kopija, kopija1, kopija2: pokCvor;
begin
  stek1:=nil;
  difstek:=nil;
  tekuci:=koren;
  while (tekuci<>nil) do
  begin
    push(stek1, tekuci);
    tekuci:=tekuci^.levi;
  end;
  empty(stek1, ans);
  while (not ans) do
  begin
    pop(stek1, novi);
    if (novi^.oznaka in dozvoljeni) then
    begin
    pomrsikonce(novi);
    push(stek1, novi);
    novi:=novi^.desni;
    while (novi<>nil) do
    begin
      push(stek1, novi);
      novi:=novi^.levi;
    end;
    empty(stek1, ans);
    end
    else
    begin
      razmrsikonce(novi);
      if (novi^.oznaka='1') or (novi^.oznaka='0') then
      begin
        difnovi:=napravicvor('0');
        push(difstek, difnovi);
      end;
      if (ord(novi^.oznaka)>=ord('A')) and (ord(novi^.oznaka)<=ord('Z')) then
      begin
        if novi^.oznaka=dif then begin
           difnovi:=napravicvor('1');
           push(difstek, difnovi);
        end
        else begin
          difnovi:=napravicvor('0');
          push(difstek, difnovi);
        end;
      end
      else begin
        case novi^.oznaka of
          '+': begin
            pop(difstek, difdrugi);
            pop(difstek, difprvi);
            difnovi:=napravicvor('+');
            difnovi^.levi:=difprvi;
            difnovi^.desni:=difdrugi;
            push(difstek, difnovi);
          end;
          '-': begin
            pop(difstek, difdrugi);
            pop(difstek, difprvi);
            difnovi:=napravicvor('-');
            difnovi^.levi:=difprvi;
            difnovi^.desni:=difdrugi;
            push(difstek, difnovi);
          end;
          '*': begin
            pop(difstek, difdrugi);
            pop(difstek, difprvi);
            difnovi:=napravicvor('+');
            difnovi^.levi:=napravicvor('*');
            difnovi^.desni:=napravicvor('*');
            dete1:=difnovi^.levi;
            dete2:=difnovi^.desni;
            dete1^.levi:=difprvi;
            kopi(novi^.desni, kopija);
            dete1^.desni:=kopija;
            dete2^.levi:=difdrugi;
            kopi(novi^.levi, kopija);
            dete2^.desni:=kopija;
            push(difstek, difnovi);
          end;
          '/': begin
            pop(difstek, difdrugi);
            pop(difstek, difprvi);
            difnovi:=napravicvor('/');
            difnovi^.desni:=napravicvor('*');
            dete1:=difnovi^.desni;
            kopi(novi^.desni, kopija);
            dete1^.levi:=kopija;
            dete1^.desni:=kopija;
            difnovi^.levi:=napravicvor('-');
            dete2:=difnovi^.levi;
            dete2^.levi:=napravicvor('*');
            dete2^.desni:=napravicvor('*');
            dete2^.levi^.levi:=difprvi;
            dete2^.levi^.desni:=kopija;
            dete2^.desni^.levi:=difdrugi;
            kopi(novi^.levi, kopija);
            dete2^.desni^.desni:=kopija;
            push(difstek, difnovi);
          end;
          'e': begin
            pop(difstek, difprvi);
            difnovi:=napravicvor('*');
            difnovi^.desni:=difprvi;
            difnovi^.levi:=napravicvor('e');
            kopi(novi^.levi, kopija);
            difnovi^.levi^.levi:=kopija;
            push(difstek, difnovi);
          end;
          'a': begin
            pop(difstek, difprvi);
            difnovi:=napravicvor('*');
            difnovi^.desni:=difprvi;
            difnovi^.levi:=napravicvor('/');
            dete1:=difnovi^.levi;
            kopi(novi^.levi, kopija);
            dete1^.levi:=napravicvor('a');
            dete1^.levi^.levi:=kopija;
            dete1^.desni:=kopija;
            push(difstek, difnovi);
          end;
          'u': begin
            pop(difstek, difprvi);
            difnovi:=napravicvor('u');
            difnovi^.levi:=difprvi;
            push(difstek, difnovi);
          end;
          'l': begin
            provera(novi^.levi, odg, dif);
            if (not odg) then
            begin
              pop(difstek, difprvi);
              pop(difstek, difdrugi);
              difnovi:=napravicvor('/');
              difnovi^.levi:=napravicvor('1');
              difnovi^.desni:=napravicvor('*');
              dete1:=difnovi^.desni;
              kopi(novi^.desni, kopija);
              dete1^.levi:=kopija;
              dete1^.desni:=napravicvor('n');
              kopi(novi^.levi, kopija);
              dete1^.desni^.levi:=kopija;
              push(difstek, difnovi);
            end
            else
            begin
              provera(novi^.desni, odg, dif);
              if (not odg) then
              begin
                pop(difstek, difprvi);
                pop(difstek, difdrugi);
                difnovi:=napravicvor('*');
                difnovi^.levi:=napravicvor('*');
                difnovi^.desni:=napravicvor('*');
                dete1:=difnovi^.levi;
                dete2:=difnovi^.desni;
                dete1^.levi:=napravicvor('n');
                kopi(novi^.desni, kopija);
                dete1^.levi^.levi:=kopija;
                dete1^.desni:=napravicvor('/');
                dete1^.desni^.levi:=napravicvor('u');
                dete1^.desni^.levi^.levi:=napravicvor('1');
                kopi(novi^.levi, kopija);
                dete1^.desni^.desni:=kopija;
                dete2^.levi:=napravicvor('n');
                dete2^.desni:=napravicvor('*');
                dete2^.levi^.levi:=kopija;
                dete2^.desni^.levi:=napravicvor('n');
                dete2^.desni^.levi^.levi:=kopija;
                dete2^.desni^.desni:=difdrugi;
                push(difstek, difnovi);
              end
              else
              begin
                pop(difstek, difprvi);
                pop(difstek, difdrugi);
                difnovi:=napravicvor('/');
                difnovi^.desni:=napravicvor('*');
                dete1:=difnovi^.desni;
                dete1^.levi:=napravicvor('n');
                dete1^.desni:=napravicvor('n');
                kopi(novi^.levi, kopija1);
                kopi(novi^.desni, kopija2);
                dete1^.levi^.levi:=kopija1;
                dete1^.desni^.levi:=kopija1;
                difnovi^.levi:=napravicvor('-');
                dete2:=difnovi^.levi;
                dete2^.levi:=napravicvor('*');
                dete2^.desni:=napravicvor('*');
                dete1:=dete2^.levi;
                dete2:=dete2^.desni;
                dete1^.levi:=napravicvor('/');
                dete1^.levi^.levi:=napravicvor('1');
                dete1^.levi^.desni:=kopija2;
                dete1^.desni:=napravicvor('*');
                dete1^.desni^.levi:=difprvi;
                dete1^.desni^.desni:=napravicvor('n');
                dete1^.desni^.desni^.levi:=kopija1;
                dete2^.levi:=napravicvor('/');
                dete2^.levi^.levi:=napravicvor('1');
                dete2^.levi^.desni:=kopija1;
                dete2^.desni:=napravicvor('*');
                dete2^.desni^.levi:=difdrugi;
                dete2^.desni^.desni:=napravicvor('n');
                dete2^.desni^.desni^.levi:=kopija2;
                push(difstek, difnovi);
              end;
            end;
          end;
          '^': begin
            provera(novi^.levi, odg, dif);
            if (not odg) then
            begin
              pop(difstek, difprvi);
              difnovi:=napravicvor('*');
              kopi(novi, kopija);
              difnovi^.levi:=kopija;
              difnovi^.desni:=napravicvor('*');
              dete1:=difnovi^.desni;
              dete1^.desni:=napravicvor('n');
              kopi(novi^.levi, kopija);
              dete1^.desni^.levi:=kopija;
              dete1^.levi:=difprvi;
              push(difstek, difnovi);
            end
            else
            begin
              pop(difstek, difprvi);
              pop(difstek, difdrugi);
              difnovi:=napravicvor('*');
              kopi(novi^.desni, kopija1);
              kopi(novi^.levi, kopija2);
              difnovi^.levi:=kopija1;
              difnovi^.desni:=napravicvor('*');
              dete1:=difnovi^.desni;
              dete1^.levi:=napravicvor('^');
              dete1^.desni:=difdrugi;
              dete2:=dete1^.levi;
              dete2^.levi:=kopija2;
              dete2^.desni:=napravicvor('-');
              dete2^.desni^.levi:=kopija1;
              dete2^.desni^.desni:=napravicvor('1');
              push(difstek, difnovi);
            end;
          end;
          'n': begin
              pop(difstek, difprvi);
              difnovi:=napravicvor('*');
              difnovi^.levi:=napravicvor('/');
              difnovi^.levi^.levi:=napravicvor('1');
              kopi(novi^.levi, kopija1);
              difnovi^.levi^.desni:=kopija1;
              difnovi^.desni:=difprvi;
              push(difstek, difnovi);
          end;
      end;
      empty(stek1, ans);
    end;
  end;
 end;
  pop(difstek, rezultat);
end;
//funkcija ispituje da li su data stabla identicna
procedure isti(var koren1: pokCvor; var koren2: pokCvor; var odg: boolean);
var
  novi1, novi2: pokCvor; stek1, stek2: pokElem; ans1, ans2: boolean;
begin
  odg:=true;
  stek1:=nil;
  stek2:=nil;
  push(stek1, koren1);
  push(stek2, koren2);
  empty(stek1, ans1);
  empty(stek2, ans2);
  while (not ans1) or (not ans2) do
  begin
    pop(stek1, novi1);
    pop(stek2, novi2);
    if ((novi1<>nil) and (novi2=nil)) or ((novi1=nil) and (novi2<>nil)) then odg:=false;
    while (novi1<>nil) and (novi2<>nil) do
    begin
      if novi1^.oznaka<>novi2^.oznaka then odg:=false;
      if (novi1^.desni<>nil) then push(stek1, novi1^.desni);
      if (novi2^.desni<>nil) then push(stek2, novi2^.desni);
      novi1:=novi1^.levi;
      novi2:=novi2^.levi;
    end;
    empty(stek1, ans1);
    empty(stek2, ans2);
  end;
end;
//procedura oslobadja memoriju koju stablo zauzima
procedure brisi(var koren: pokCvor);
var
  novi, tekuci: pokCvor; stek: pokElem; ans: boolean;
begin
  stek:=nil;
  push(stek, koren);
  empty(stek, ans);
  while (not ans) do
  begin
    pop(stek, novi);
    while (novi<>nil) do
    begin
      if (novi^.desni<>nil) then push(stek, novi^.desni);
      tekuci:=novi;
      novi:=novi^.levi;
      dispose(tekuci);
    end;
    empty(stek, ans);
  end;
end;
{funkcija prolazi postorderom diferencirano stablo i nalazi sve sto se moze
pojednostaviti u njemu - podizraze kao sto su 0+X, 0*X itd. menja sa X i 0 npr.
cime se znacajno smanjuje prostor koji stablo zauzima i umnogome olaksava racunanje
daljih izvoda - primer bi bila funkcija log(A,A) po A, gde izvod ima 20ak cvorova
dok se ne pojednostavi u 0; naravno, odmah se da primetiti da je ovo konstanta i
izvod je 0, ali u funkciji za diferenciranje se obradjuju opsti slucajevi pa ovo
nije obezbedjeno, dok ova funkcija sluzi tome da pojednostavi dobijena stabla koliko
je god moguce}
procedure sredjivanje(var koren: pokCvor; var novikoren:pokCvor);
var
  stek1, stek2: pokElem; tekuci, novi, prvi, drugi, pravi: pokCvor; ans, odg: boolean;
begin
  stek1:=nil;
  stek2:=nil;
  tekuci:=koren;
  while (tekuci<>nil) do
  begin
    push(stek1, tekuci);
    tekuci:=tekuci^.levi;
  end;
  empty(stek1, ans);
  while (not ans) do
  begin
    pop(stek1, novi);
    if (novi^.oznaka in dozvoljeni) then
    begin
    pomrsikonce(novi);
    push(stek1, novi);
    novi:=novi^.desni;
    while (novi<>nil) do
    begin
      push(stek1, novi);
      novi:=novi^.levi;
    end;
    empty(stek1, ans);
    end
    else
    begin
      razmrsikonce(novi);
      if ((ord(novi^.oznaka)>=ord('A')) and (ord(novi^.oznaka)<=ord('Z')))
      or (novi^.oznaka='0') or (novi^.oznaka='1') then
      begin
        prvi:=napravicvor(novi^.oznaka);
        push(stek2, prvi);
      end
      else case novi^.oznaka of
        '+': begin
          pop(stek2, prvi);
          pop(stek2, drugi);
          if drugi^.oznaka='0' then
          begin
            push(stek2, prvi);
            brisi(drugi);
          end
          else if prvi^.oznaka='0' then
          begin
            brisi(prvi);
            push(stek2, drugi);
          end
          else if drugi^.oznaka='u' then
          begin
            isti(prvi, drugi^.levi, odg);
            if odg then begin
              brisi(prvi);
              brisi(drugi);
              prvi:=napravicvor('0');
              push(stek2, prvi);
            end;
          end
          else if prvi^.oznaka='u' then
          begin
            isti(drugi, prvi^.levi, odg);
            if odg then begin
              brisi(prvi);
              brisi(drugi);
              prvi:=napravicvor('0');
              push(stek2, prvi);
            end;
          end
          else
          begin
            pravi:=napravicvor('+');
            pravi^.levi:=drugi;
            pravi^.desni:=prvi;
            push(stek2, pravi);
          end;
        end;
        '-': begin
          pop(stek2, prvi);
          pop(stek2, drugi);
          isti(drugi, prvi, odg);
          if odg then begin
            brisi(prvi);
            brisi(drugi);
            prvi:=napravicvor('0');
            push(stek2, prvi);
          end
          else if drugi^.oznaka='0' then
          begin
            brisi(drugi);
            drugi:=napravicvor('u');
            drugi^.levi:=prvi;
            push(stek2, drugi);
          end
          else if prvi^.oznaka='0' then
          begin
            brisi(prvi);
            push(stek2, drugi);
          end
          else
          begin
            pravi:=napravicvor('-');
            pravi^.levi:=drugi;
            pravi^.desni:=prvi;
            push(stek2, pravi);
          end;
        end;
        '*': begin
           pop(stek2, prvi);
           pop(stek2, drugi);
           if (drugi^.oznaka='0') or (prvi^.oznaka='0') then
           begin
             brisi(prvi);
             brisi(drugi);
             prvi:=napravicvor('0');
             push(stek2, prvi);
           end
           else if (drugi^.oznaka='1') then
           begin
             push(stek2, prvi);
             brisi(drugi);
           end
           else if (prvi^.oznaka='1') then
           begin
             push(stek2, drugi);
             brisi(prvi);
           end
           else
           begin
             pravi:=napravicvor('*');
             pravi^.levi:=drugi;
             pravi^.desni:=prvi;
             push(stek2, pravi);
           end;
        end;
        'n': begin
          pop(stek2, prvi);
          drugi:=napravicvor('n');
          drugi^.levi:=prvi;
          push(stek2, drugi);
        end;
        '/': begin
          pop(stek2, prvi);
          pop(stek2, drugi);
          isti(prvi,drugi,odg);
          if (drugi^.oznaka='0') then
          begin
            brisi(prvi);
            brisi(drugi);
            prvi:=napravicvor('0');
            push(stek2, prvi);
          end
          else if (prvi^.oznaka='1') then
          begin
            brisi(prvi);
            push(stek2, drugi);
          end
          else if odg then
          begin
            brisi(prvi);
            brisi(drugi);
            prvi:=napravicvor('1');
            push(stek2, prvi);
          end
          else
          begin
            pravi:=napravicvor('/');
            pravi^.levi:=drugi;
            pravi^.desni:=prvi;
            push(stek2, pravi);
          end;
        end;
        '^': begin
          pop(stek2, prvi);
          pop(stek2, drugi);
          if (prvi^.oznaka='0') then
          begin
            brisi(prvi);
            brisi(drugi);
            prvi:=napravicvor('1');
            push(stek2, prvi);
          end
          else if (prvi^.oznaka='1') then
          begin
            brisi(prvi);
            push(stek2, drugi);
          end
          else if (drugi^.oznaka='1') then
          begin
            brisi(prvi);
            push(stek2, drugi);
          end
          else if (drugi^.oznaka='0') then
          begin
            brisi(prvi);
            push(stek2, drugi);
          end
          else
          begin
            pravi:=napravicvor('^');
            pravi^.levi:=drugi;
            pravi^.desni:=prvi;
            push(stek2, pravi);
          end;
        end;
        'u': begin
          pop(stek2, prvi);
          if (prvi^.oznaka='u') then push(stek2, prvi^.levi)
          else
          begin
            drugi:=napravicvor('u');
            drugi^.levi:=prvi;
            push(stek2, drugi);
          end;
        end;
        'a': begin
          pop(stek2, prvi);
          if (prvi^.oznaka='a') then
          begin
            drugi:=napravicvor('a');
            drugi^.levi:=prvi^.levi;
            push(stek2, drugi);
          end
          else if (prvi^.oznaka='1') or (prvi^.oznaka='0') then
          begin
            push(stek2, prvi);
          end
          else
          begin
            drugi:=napravicvor('a');
            drugi^.levi:=prvi;
            push(stek2, drugi);
          end;
        end;
        'l': begin
          pop(stek2, prvi);
          pop(stek2, drugi);
          isti(prvi, drugi, odg);
          if (odg) then
          begin
            brisi(prvi);
            brisi(drugi);
            prvi:=napravicvor('1');
            push(stek2, prvi);
          end
          else if prvi^.oznaka='1' then
          begin
            brisi(prvi);
            brisi(drugi);
            prvi:=napravicvor('0');
            push(stek2, prvi);
          end
          else
          begin
            pravi:=napravicvor('l');
            pravi^.levi:=drugi;
            pravi^.desni:=prvi;
            push(stek2, pravi);
          end;
        end;
        'e': begin
          pop(stek2, prvi);
          if prvi^.oznaka='0' then
          begin
            push(stek2, prvi);
          end
          else
          begin
            drugi:=napravicvor('e');
            drugi^.levi:=prvi;
            push(stek2, drugi);
          end;
        end;
      end;
      empty(stek1, ans);
end;
end;
  pop(stek2, novikoren);
end;
{jednostavnim menijem se odabira jedna od ponudjenih opcija; kada se pozove opcija
5, postoji i dodatni podmeni jer je moguce da se racuna i vrednost diferenciranog
stabla, kao i neki drugi izvod od prethodno vec izracunatog izvoda; izvodi se
prikazuju u obliku ispisanog stabla, a ne u obliku izraza}
begin
  ulaz:=6;
  koren:=nil;
  repeat
    write('Ispred sebe imate ponudjeni meni. Slanjem broja ispred stavke u');
    writeln(' meniju i pritiskom tastera ENTER birate jednu od opcija.');
    writeln('1. Unos izraza');
    writeln('2. Ispis stabla');
    writeln('3. Ispis izraza u prefiksnom obliku');
    writeln('4. Racunanje vrednosti izraza uz unos promenljivih');
    writeln('5. Diferenciranje izraza po zadatoj promenljivoj');
    writeln('6. Izlaz iz programa');
    readln(ulaz);
    case ulaz of
      1: begin
        writeln('Izabrali ste unos izraza. Izraz se unosi u infiksnom obliku, sa promenljivama u obliku velikih slova.');
        writeln('Izraz moze sadrzati zagrade, kao i sledece operacije: +, -, *, /, ^, za koje unosite podizraze u obliku A op B.');
        writeln('Za unarni minus unesite podizraz u obliku (-A). Za eksponencijalnu funkciju unesite podizraz u obliku exp(A). ');
        writeln('Za apsolutnu vrednost unesite podizraz u obliku abs(A).');
        writeln('Za logaritam unesite podizraz u obliku log(A,B), gde je A osnova.');
        writeln('Ako su A i B takodje podizrazi, unesite ih sa zagradama - log((A),(B)).');
        readln(izraz);
        if (koren<>nil) then brisi(koren);
        pravistablo(koren, izraz);
      end;
      2: begin
        writeln('Izabrali ste ispis stabla. Stablo se ispisuje indentacijom.');
        ispisstabla(koren);
        writeln;
      end;
      3: begin
        writeln('Izabrali ste prefiksni ispis izraza, koji glasi:');
        preorder(koren);
        writeln;
      end;
      4: begin
        writeln('Izabrali ste racunanje vrednosti izraza.');
        writeln('Prvo unesite vrednosti svih promenljivih koje figurisu u izrazu u obliku X=V, gde je X slovo, a V vrednost.');
        writeln('Unosite u svakom redu po jednu promenljivu. Kada zavrsite sa unosom, dva puta pritisnite ENTER.');
        readln(red);
        repeat
          neg:=false;
          prom:=red[1];
          i:=3;
          a:=0;
          if red[3]='-' then begin
            i:=i+1;
            neg:=true;
          end;
          while i<=length(red) do begin
            a:=10*a+ord(red[i])-ord('0');
            i:=i+1;
          end;
          if not neg then vrednosti[ord(prom)-ord('A')+1]:=a
          else vrednosti[ord(prom)-ord('A')+1]:=-a;
          readln(red);
        until red='';
        racunanje(koren, vrednosti, rezultat);
        writeln('Izraz ima vrednost: ', rezultat:2:2);
      end;
      5: begin
        writeln('Unesite promenljivu po kojoj zelite da diferencirate izraz:');
        readln(dif);
        writeln('Unesite koji izvod zelite (1 za prvi, 2 za drugi itd.):');
        readln(brojizvoda);
        difprethodni:=koren;
        for i:=1 to brojizvoda do
        begin
          diferenciranje(difprethodni, difrezultat, dif);
          brisi(difprethodni);
          sredjivanje(difrezultat, difprethodni);
        end;
        sredjivanje(difrezultat, sredjen);
        writeln('Diferencirano stablo izgleda:');
        ispisstabla(difrezultat);
        writeln('Kada se ovo stablo sredi, dobije se pojednostavljeni izvod:');
        ispisstabla(sredjen);
        repeat
        writeln('Sada imate jos izbora. Mozete birati:');
        writeln('1. Izracunavanje nekog drugog izvoda osnovnog izraza');
        writeln('2. Racunanje vrednosti obradjenog izvoda');
        writeln('3. Povratak na glavni meni:');
        readln(podizbor);
        case podizbor of
          1: begin
               writeln('Unesite promenljivu po kojoj zelite da diferencirate izraz:');
               readln(dif);
               writeln('Unesite koji izvod zelite (1 za prvi, 2 za drugi itd.):');
               readln(brojizvoda);
               difprethodni:=koren;
               for i:=1 to brojizvoda do
               begin
                    diferenciranje(difprethodni, difrezultat, dif);
                    brisi(difprethodni);
                    sredjivanje(difrezultat, difprethodni);
               end;
               sredjivanje(difrezultat, sredjen);
               writeln('Diferencirano stablo izgleda:');
               ispisstabla(difrezultat);
               writeln('Kada se ovo stablo sredi, dobije se pojednostavljeni izvod:');
               ispisstabla(sredjen);
          end;
          2: begin
               writeln('Prvo unesite vrednosti svih promenljivih koje figurisu u izrazu u obliku X=V, gde je X slovo, a V vrednost.');
               writeln('Unosite u svakom redu po jednu promenljivu. Kada zavrsite sa unosom, dva puta pritisnite ENTER.');
               readln(red);
               repeat
                     prom:=red[1];
                     i:=3;
                     a:=0;
               while i<=length(red) do begin
               a:=10*a+ord(red[i])-ord('0');
               i:=i+1;
               end;
               vrednosti[ord(prom)-ord('A')+1]:=a;
               readln(red);
               until red='';
               racunanje(sredjen, vrednosti, rezultat);
               writeln('Izraz ima vrednost: ', rezultat:2:2);
          end;
        end;
        until podizbor=3;
      end;
  end;
  until ulaz=6;
end.
