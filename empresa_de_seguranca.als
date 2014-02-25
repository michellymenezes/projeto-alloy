module empresaDeSeguranca

sig bairro{
	casas: set casa
}

one sig autoBranco extends bairro{}

one sig centro extends bairro{}

// Fato sobre bairro
fact nomeBairro {
	all b: bairro | some b.casas
	centro in bairro
	autoBranco in bairro
}

sig casa{}

fact sobreCasa{
	all c:casa | some c.servico
	all c:casa | one c.servico
}

abstract sig servico{}

sig cercaEletrica extends servico{}

sig rondaNoturna extends servico{}

sig monitoramentoCameras extends servico{}

fact sobreServico{
	all r: rondaNoturna | some r.cercaEletrica
}

pred show[]{}
run show for 3
