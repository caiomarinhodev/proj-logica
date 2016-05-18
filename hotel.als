--Duvidas
-- FEITO O Hotel tem um numero limitado de Hospedes? Sim Numero pequeno
-- FEITO No quarto Triplo, pode se hospedar quantas pessoas no m[inimo? Pode se hospedar uma
-- FEITO Uma crian;a pode estar hospedade sozinha? Nao
-- FEITO No completo, todas as refeicoes significa cafe almoco e janta? Sim
-- FEITO Funcoes: criancas[Hospedagem], adultos[Hospedagem], hospedagemReserva
-- FEITO Conjunto de reservas canceladas existe
-- FEITO Alimentacao [e pra cada pessoa ou pro quarto? quarto. Fizemos como se soh existe um tipo de alimentacao pro predio todo
-- FEITO Crianca tem um Responsavel? Nao Mas ela soh pode estar num quarto com adulto
-- FEITO Reserva eh individual ou feita pra um quarto? quarto
-- FEITO Pode ter soh crianca em um quarto? Nao
-- FEITO Se tiver uma crianca num quarto, precisa ter o responsavel nela? Nao, soh precisa ter adulto
-- FEITO Precisa colocar Cartao de Credito? Ja que essa eh a unica forma de fazer uma reserva
---------- Reserva usa cartao de credito, pois existe hospedagem
-- FEITO Tem que criar uma Hospedagem, pois a reserva nao significa que esta hospedado.
-- FEITO Criancas nao diminuem as vagas dos adultos.
open util/ordering [Time]
sig Time {}

sig Hotel {
	hospedagens: Hospedagem -> Time,
	hospedes: Hospede -> Time,
	reservas: Reserva -> Time,
	hospedagensPassadas: Hospedagem -> Time
}

abstract sig Hospede {}
sig HospedeAdulto extends Hospede{}
sig HospedeCrianca extends Hospede{}

sig Hospedagem {
	titular: one Hospede,
	reserva: lone Reserva,
	quarto: one Quarto,
	dependentes: some Hospede,
	formaPagamento: one FormaPagamento,
	tipoAlimentacao: one Alimentacao
}

abstract sig FormaPagamento {}
sig Dinheiro extends FormaPagamento {}
sig CartaoCredito extends FormaPagamento {}

abstract sig Quarto {}
sig QuartoDuplo extends Quarto {}
sig QuartoTriplo extends Quarto {}

-- Fatos e predicados de Quarto
fact QuartoFact {
	all r: Reserva, h: Hospedagem |
		h.reserva != r => r.quarto != h.quarto
	
	all h1, h2: Hospedagem |
		h1 != h2 => h1.quarto != h2.quarto

	all r1, r2: Reserva |
		r1 != r2 => r1.quarto != r2.quarto
}

abstract sig Alimentacao {}
sig Cafe {}
sig Almoco  {}
sig Janta {}
sig ApenasCafe extends Alimentacao {
	cafe: one Cafe
}
sig MeiaPensao extends Alimentacao {
	cafe: one Cafe,
	janta: one Janta
}
sig PensaoCompleta extends Alimentacao{
	cafe: one Cafe,
	almoco: one Almoco,
	janta: one Janta
}

sig Reserva {
	tipoAlimentacao: one Alimentacao,
	quarto: one Quarto,
	titular: one Hospede,
	formaPagamento: lone CartaoCredito
}
sig ReservaTresDias extends Reserva {}
sig ReservaCancelada extends Reserva {}
sig ReservaNaoApareceu extends Reserva {}

-- Fatos e predicados de Reserva
pred ehReservaCancelada[r: Reserva] {
	r in ReservaCancelada
}
fun hospedagemReserva[r: Reserva]: Hospedagem {
	r.~reserva
}
fact ReservaFact {
	all r: Reserva |
		r.titular !in HospedeCrianca
	
	all r: Reserva |
		ehReservaCancelada[r] <=> no r.formaPagamento

	all r: Reserva |
		!ehReservaCancelada[r] => one r.formaPagamento

	all r: Reserva |
		(r in ReservaCancelada or r in ReservaNaoApareceu)
			<=> no hospedagemReserva[r]

	all r: ReservaTresDias |
		r.tipoAlimentacao in MeiaPensao
		or r.tipoAlimentacao in PensaoCompleta
}

-- Fatos e predicados de Hospede
pred hospedeTemUmaHospedagem[h: Hospede] {
	one h.~dependentes
}
pred hospedeTitularReserva[h: Hospede, r: Reserva] {
	r.titular = h
}
pred hospedeTitularHospedagem[h: Hospede, o: Hospedagem] {
	o.titular = h
}
fun hospedagemDoHospede[h: Hospede] : Hospedagem {
	dependentes.h
}
fact HospedeFact {
	all h: Hospede |
		hospedeTemUmaHospedagem[h]
			or
		(some r: Reserva | hospedeTitularReserva[h, r])

	all h: Hospede, r1,r2: Reserva |
		(r1 != r2 and hospedeTitularReserva[h, r1])
			=> !hospedeTitularReserva[h, r2]
}


-- Fatos e predicados de Hospedagem
pred mesmoTitular[h: Hospedagem, r: Reserva] {
	h.titular = r.titular
}
pred mesmoQuarto[h: Hospedagem, r: Reserva] {
	h.quarto = r.quarto
}
pred mesmaFormaPagamento[h: Hospedagem, r: Reserva] {
	h.formaPagamento = r.formaPagamento
}
pred mesmoTipoAlimentacao[h: Hospedagem, r: Reserva] {
	h.tipoAlimentacao = r.tipoAlimentacao
}
fun criancas[h: Hospedagem]: HospedeCrianca {
	--e1 :> e2: range restriction of e1 to e2;
	--The range restriction of e1 to e2 contains all
	--tuples in e1 that end with an element in the set e2. 
	h.(dependentes :> HospedeCrianca)
}
fun adultos[h: Hospedagem]: Hospede {
	h.(dependentes :> HospedeAdulto)	
}
fact HospedagemFact {
	all h: Hospedagem, r: Reserva |
		(h.reserva = r => mesmoTitular[h, r])
		and
		(mesmoTitular[h, r]
			=> h.reserva = r and mesmoQuarto[h, r]
				and mesmaFormaPagamento[h, r])
	
	all h: Hospedagem, r: Reserva |
		h.reserva != r => r.titular !in h.dependentes

	all h: Hospedagem |
		h.titular in h.dependentes
		and h.titular !in HospedeCrianca
		and (some ReservaCancelada => h.reserva !in ReservaCancelada) --Fiz assim pq ele considera falso !in pra um conjunto Vazio eh tipo como se todo elemento estivesse in um conjunto vazio

	all h1,h2: Hospedagem, t: Time |
		(h1 != h2 and (h1 -> t in Hotel.hospedagens and h2 -> t in Hotel.hospedagens))
			=> no h1.dependentes & h2.dependentes
	
	all h: Hospedagem |
		(h.quarto in QuartoDuplo =>
			#(adultos[h]) <= 2
			and #(criancas[h]) <= 1)
		and
		(h.quarto in QuartoTriplo =>
			#(adultos[h]) <= 3
			and #(criancas[h]) <= 2)
}

--Operacoes
pred registrarHospedagem[o: Hotel, h: Hospedagem, t,t': Time] {
	h !in (o.hospedagens).t
	(o.hospedagens).t' = (o.hospedagens).t + h
}
-- Os hospedes sao registrados ao mesmo tempo que uma hospedagem eh registrada
pred checkInHospedes[o: Hotel, hos: Hospede, t,t': Time] {
	hos !in (o.hospedes).t
	(o.hospedes).t' = (o.hospedes).t + hos
}
pred checkOutHospedes[o: Hotel, hos: Hospede, t,t': Time] {
	hos in (o.hospedes).t
	(o.hospedes).t' = (o.hospedes).t - hos
}
pred encerrarHospedagem[o: Hotel, h: Hospedagem, t,t': Time] {
	h in (o.hospedagens).t
	h !in (o.hospedagensPassadas).t

	(o.hospedagens).t' = (o.hospedagens).t - h
	(o.hospedagensPassadas).t' = (o.hospedagensPassadas).t + h
}

--Traces
pred init[t:Time] {
	no (Hotel.hospedagens).t
	no (Hotel.hospedagensPassadas).t
	no Hotel.reservas
	no (Hotel.hospedes).t
}
fact Traces {
	init[first]
	all pre: Time-last | let pos = pre.next |
		some h: Hospedagem, o: Hotel|
			    registrarHospedagem[o, h, pre, pos]
			    and
			    checkInHospedes[o, h.dependentes, pre, pos]
}

-- Fatos Que tem uma quantidade fixada no projeto
fact ConstantFacts {
	#(Hotel) = 1
	#(Cafe) = 1
	#(Almoco) = 1
	#(Janta) = 1
	#(ApenasCafe) = 1
	#(MeiaPensao) = 1
	#(PensaoCompleta) = 1
	#(CartaoCredito) = 1
	#(Dinheiro) = 1
}

pred show[] {}

run show for 4
