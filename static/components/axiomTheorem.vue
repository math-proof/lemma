<template>
	<icon ref=icon class=theorem :text=theorem :lines=5 :index=index></icon>
</template>

<script>
import icon from "./icon.vue"
console.log('import axiomTheorem.vue');

export default {
	components: {icon},
	
	props : [ 'theorem', 'index'],
	
	created() {
		this.$parent.axiomTheorem[this.index] = this;	
	},
	
	methods: {
		dblclick(event) {
			var self = event.target;
			var text = self.textContent;
			text = text.trim();
			var search = location.search;
			if (search.indexOf('.') >= 0){
				if (search.endsWith('.'))
					search += text;
				else
					search += '.' + text;
			}
			else{
				if (search.endsWith('/'))
					search += text;
				else
					search += '/' + text;
			}
			
			location.href = location.origin + location.pathname + search;
		},			

		remove() {
			console.log("this.theorem = " + this.theorem);
			var href = location.href;
			var m = href.match(/\/([^\/]+)\/(?:index\.php)?\?module=([^#]+)/);
			var module = m[2];
			module = module.replace(/\//g, '.').replace(/%27/g, "'");
			if (module.endsWith('.'))
				module = module.slice(0, -1);

			var data = {};
			data['package'] = module;
			data['lemma'] = this.theorem;
			form_post(`php/request/delete/lemma.php`, data).then(res => {
				console.log('res = ' + res);
			});
		},
	}		
}
</script>

<style>
.theorem {
	width: 3.2em;
	height: 5em;
	border-top: 0.4em solid #003;
	border-bottom: 0.4em solid #003;
	border-left: 0.4em solid #003;
	margin: 50px auto;
	position: relative;
}

div .theorem {
	display: inline-block;
	background: rgb(220, 220, 0);
	text-align: center;
	margin-right: 3em;
}

.theorem:before {
	border-right: 0.4em solid #001;
	border-bottom: 0.4em solid #001;
	width: 1em;
	height: 4em;
	position: absolute;
	right: -1.3em;
	bottom: -0.4em;
	content: "";
	background: rgb(220, 220, 0);
}

.theorem:after {
	position: absolute;
	top: -0.4em;
	right: -1.3em;
	content: "";
	border-bottom: 1.4em solid #003;
	border-right: 1.4em solid transparent;
	width: 0;
	height: 0;
}
</style>