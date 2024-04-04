Rust on üldotstarbeline programeerimise keel nii süsteemi kui ka rakenduste tarkvara loomiseks.
Erinevalt teistest programeerimise keeltest suudab Rust garanteerida turvalise mälu kasutuse ilma kasutamata spetsiaalset mälu haldurit.
Rust üritab konkureerida programeerimise keeltega C ja C++ olles nendega sama kiire, kuid samal ajal pakkudes arendajale paremaid tööriistu ja paremat arenduse kogemust.

Rusti tüübi süsteem sarnaneb funktsionaalsete keelte tüübi süsteemidele sisaldades algebralise andmetüüpe.
Arendaja kogemus Rustis sarnaneb seetõttu rohkem kogemusele kõrgematasemelistes funktsionaalsetes programmeerimise keeltes kui kogemusele C/C++ arenduses.
Samas Rustis puudub hetkel tööriist, mis suudaks automaatselt genereerida avaldisi, mis vastavad oodatud tüübile.
Sellised tööriistad on tavalised funktsionaalsetes programmeerimise keeltes ja me usume, et ka Rustil on taolisest tööriistast kasu.

Käesolevas töös arendame edasi Rusti ametlikku tööriista `rust-analyzer` lisades sellele võimekuse genereerida avaldis tüüpide põhjal.
Lisaks programmide genereerimisele uurime, kas avaldise otsingut on võimalik kasutada ka targema automaatse sõnalõpetuse loomiseks.
Me arendama oma algorütmi kolme iteratsioonina.
Esimene iteratsioon on kõige lihtsam ja sarnaneb väga algorütmile mida kasutatakse Agsys, sarnases tööristas Agda jaoks.
Teises iteratsioonis arendame edasi algorütmi muutes otsingu suuna vastupidiseks.
Sooritades otsingut vastupidises suunas saame me lihtsalt lisada vahepealsete väärtuste puhverdamise ja ka teisi optimeerimisi.
Viimases versioonis muudame me otsingu kahesuunaliseks.
Sooritades otsingut kahes suunas suudame leida avaldise rohkemates kohtades ilma oluliselt aglustamata algorüthmi tööd.

Töö tulemuste hindamiseks jooksutame me seda 155-l vabavaralisel Rusti programmil.
Me kustutame osa olemasolevast lähtekoodist jättes programmi koodi "augud".
Nüüd kasutame me oma algorütmi et genereerida kood nende aukude jaoks.
Me mõõdame kui paljusi auke suudab algorütm täita ja kui tihti suudab algoritm genereerida tagasi originaalse lähtekoodi.

Töö väljundina saame oma algorütmi ametlikku `rust-analyzer`'i, et seda saaks kasutada kõik Rusti arendajad.

Lõputöö on kirjutatud inglise keeles keeles ning sisaldab tekst #context counter(page).at(<end>).first() leheküljel, 
#context counter(heading).at(<conclusion>).first() peatükki,
#context counter(figure.where(kind: image)).final().first() joonist 
#context counter(figure.where(kind: raw)).final().first() koodinäidist ja
#context counter(figure.where(kind: table)).final().first() tabelit.