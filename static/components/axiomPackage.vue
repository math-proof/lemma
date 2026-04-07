<template>
	<icon ref=icon class=package :text=module :lines=3 :index=index></icon>
</template>

<script>
import icon from "./icon.vue"
console.log('import axiomPackage.vue');

export default {
	components: {icon},

	props : ['module', 'index'],

	created() {
		this.$parent.axiomPackage[this.index] = this;	
	},
	
	methods : {
		dblclick(event) {
			var self = event.target;
			var text = self.textContent;
			text = text.trim(); 
			var search = location.search;
			if (search.indexOf('.') >= 0){
				if (search.endsWith('.'))
					search += text + '.';
				else
					search += '.' + text + '.';
			}
			else{
				if (search.endsWith('/'))
					search += text + '/';
				else
					search += '/' + text + '/';
			}

			location.href = location.origin + location.pathname + search;
		},
		
		remove() {
			console.log("this.module = " + this.module);
			// `php/request/delete/package.php` expects `package` (parent module) + `section` (folder name).
			var u = new URL(location.href);
			var pkg = (u.searchParams.get('module') || '').replace(/\//g, '.').trim();
			pkg = pkg.replace(/\.+$/, '');
			var data = { package: pkg, section: this.module };
			form_post('php/request/delete/package.php', data).then(res => {
				console.log('res = ' + res);
			});
		},
	}
}
</script>

<style>

.package {
	width: 5em;
	height: 3em;
	margin: 50px auto;
	position: relative;
	height: 3em;
	z-index: 1;
}

div .package {
	display: inline-block;
	background: rgb(220, 220, 0);
	text-align: center;
	margin-right: 1.6em;
	background: rgb(220, 220, 0);
	border-top-left-radius: 0.3em;
	border-top-right-radius: 0.3em;
}

.package:before {
	width: 3em;
	height: 1em;
	position: absolute;
	left: 0.3em;
	top: -0.7em;
	content: "";
	background: rgb(220, 180, 0);
	border-top-left-radius: 0.3em;
	border-top-right-radius: 0.3em;
	box-shadow: 0.2em 0.2em 0 0 #9da0a0;
	z-index: 0;
}

.package:after {
	position: absolute;
	content: "";
}

</style>